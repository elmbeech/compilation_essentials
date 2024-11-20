import sys
sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')
from ast import *
from math import floor
from utils import *
from x86_ast import *
from var import Temporaries
import loop
import typing
from typing import List, Dict, Set
from graph import UndirectedAdjList
from register_allocator \
    import registers, registers_for_alloc, callee_save_for_alloc
import type_check_Ltup
import type_check_Ctup
import interp_Ltup
import interp_Ctup
from racket_interp_x86 import *

class Tuples(loop.WhileLoops):

    ###########################################################################
    # Shrink
    ###########################################################################

    def shrink_exp(self, e: expr) -> expr:
      match e:
        case Tuple(es, Load()):
          new_es = [self.shrink_exp(e) for e in es]
          return Tuple(new_es, Load())
        case Subscript(tup, index, Load()):
          return Subscript(self.shrink_exp(tup), self.shrink_exp(index), Load())
        case _:
          return super().shrink_exp(e)

    ###########################################################################
    # Expose Allocation
    ###########################################################################

    def expose_allocation(self, p: Module) -> Module:
      match p:
        case Module(body):
          return Module([self.expose_alloc_stmt(s) for s in body])

    def expose_alloc_stmt(self, s: stmt) -> stmt:
        match s:
            case Assign(targets, value):
                return Assign(targets, self.expose_alloc_exp(value))
            case Expr(value):
                return Expr(self.expose_alloc_exp(value))
            case If(test, body, orelse):
                return If(self.expose_alloc_exp(test),
                          [self.expose_alloc_stmt(s) for s in body],
                          [self.expose_alloc_stmt(s) for s in orelse])
            case While(test, body, []):
                return While(self.expose_alloc_exp(test),
                             [self.expose_alloc_stmt(s) for s in body], [])
            case _:
                raise Exception('expose_alloc_stmt: unexpected ' + repr(s))

    def expose_alloc_tuple(self, es, tupleType, allocExp):
        n = len(es)
        size = (n + 1) * 8
        vec = generate_name('alloc')
        freeptr_size = BinOp(GlobalValue('free_ptr'), Add(), Constant(size))
        space_left = Compare(freeptr_size, [Lt()],
                             [GlobalValue('fromspace_end')])
        xs = [Name(generate_name('init')) for e in es]
        inits = [Assign([x], e) for (x,e) in zip(xs,es)]
        initVec = []
        i = 0
        for x in xs:
            initVec += [Assign([Subscript(Name(vec), Constant(i),Store())], x)]
            i += 1
        return Begin(inits \
                     + [If(space_left, [], [Collect(size)])] \
                     + [Assign([Name(vec)], allocExp)] \
                     + initVec,
                     Name(vec))

    def expose_alloc_exp(self, e: expr) -> expr:
        match e:
            case Name(id):
                return e
            case Constant(value):
                return e
            case BinOp(left, op, right):
                l = self.expose_alloc_exp(left)
                r = self.expose_alloc_exp(right)
                return BinOp(l, op, r)
            case UnaryOp(op, operand):
                rand = self.expose_alloc_exp(operand)
                return UnaryOp(op, rand)
            case Call(func, args):
                fun = self.expose_alloc_exp(func)
                new_args = [self.expose_alloc_exp(arg) for arg in args]
                return Call(fun, new_args)
            case IfExp(test, body, orelse):
                tst = self.expose_alloc_exp(test)
                bod = self.expose_alloc_exp(body)
                els = self.expose_alloc_exp(orelse)
                return IfExp(tst, bod, els)
            case Begin(body, result):
                new_body = [self.expose_alloc_stmt(s) for s in body]
                new_result = self.expose_alloc_exp(result)
                return Begin(new_body, new_result)
            case Compare(left, [op], [right]):
                l = self.expose_alloc_exp(left);
                r = self.expose_alloc_exp(right)
                return Compare(l, [op], [r])
            case Tuple(es, Load()):
                new_es = [self.expose_alloc_exp(e) for e in es]
                alloc = Allocate(len(new_es), e.has_type)
                return self.expose_alloc_tuple(new_es, e.has_type, alloc)
            case Subscript(tup, index, Load()):
                return Subscript(self.expose_alloc_exp(tup),
                                 self.expose_alloc_exp(index),
                                 Load())
            case _:
                raise Exception('expose_alloc_exp: unexpected ' + repr(e))

    ###########################################################################
    # Remove Complex Operands
    ###########################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr,Temporaries]:
      match e:
        # Begin handled here because previous pass now adds Begin
        case Begin(body, result):
          sss = [self.rco_stmt(s) for s in body]
          (new_result, bs) = self.rco_exp(result, False)
          ss = make_assigns(bs)
          new_e = Begin(sum(sss, []) + ss, new_result)
          if need_atomic:
            tmp = Name(generate_name('tmp'))
            return (tmp, [(tmp, new_e)])
          else:
            return (new_e, [])
        case GlobalValue(name):
          return (e, [])      
        case Allocate(length, ty):
          if need_atomic:
            tmp = Name(generate_name('tmp'))
            return (tmp, [(tmp, e)])
          else:
            return (e, [])
        case Subscript(tup, index, Load()):
          (new_tup, bs1) = self.rco_exp(tup, True)
          (new_index, bs2) = self.rco_exp(index, True)
          new_e = Subscript(new_tup, new_index, Load())
          if need_atomic:
              tmp = Name(generate_name('tmp'))
              return (tmp, bs1 + bs2 + [(tmp, new_e)])
          else:
              return (new_e, bs1 + bs2)
        case _:
          return super().rco_exp(e, need_atomic)

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Assign([Subscript(tup, index, Store())], value):
                new_tup, bs1 = self.rco_exp(tup, True)
                new_value, bs2 = self.rco_exp(value, True)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs1] \
                    + [Assign([lhs], rhs) for (lhs, rhs) in bs2] \
                    + [Assign([Subscript(new_tup, index, Store())], new_value)]
            case Collect(amount):
                return [Collect(amount)]
            case _:
                return super().rco_stmt(s)
      
  ############################################################################
  # Explicate Control
  ############################################################################

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Subscript(tup, index, Load()):
                tmp = generate_name('tmp')
                assn = [Assign([Name(tmp)], cnd)]
                return assn + self.generic_explicate_pred(Name(tmp), thn, els,
                                                          basic_blocks)
            case _:
                return super().explicate_pred(cnd, thn, els, basic_blocks)
            
    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Collect(amount):
                return [Collect(amount)] + cont
            case _:
                return super().explicate_stmt(s, cont, basic_blocks)
          
    ###########################################################################
    # Select Instructions
    ###########################################################################

    def select_op(self, op: operator) -> str:
      match op:
        case Is():
          return 'e'
        case _:
          return super().select_op(op)
          
    def is_root_type(self, t):
      match t:
        case TupleType(ts):
          return True
        case _:
          return False

    def select_arg(self, a: expr) -> arg:
      match a:
        case GlobalValue(name):
          return Global(name)
        case _:
          return super().select_arg(a)
      
    def select_stmt(self, s: stmt) -> List[instr]:
      match s:
        case Assign([lhs], Allocate(length, TupleType(ts))):
            new_lhs = self.select_arg(lhs)
            size = 8 * (length + 1)
            is_not_fwd_tag = 1
            length_tag = length << 1
            ptr_tag = 0
            i = 7
            for t in ts:
                ptr_tag |= bool2int(self.is_root_type(t)) << i
                i = i + 1
            tag = ptr_tag | length_tag | is_not_fwd_tag
            return [Instr('movq', [Global('free_ptr'),
                                   Reg('r11')]),
                    Instr('addq', [Immediate(size),
                                   Global('free_ptr')]),
                    Instr('movq', [Immediate(tag), Deref('r11', 0)]),
                    Instr('movq', [Reg('r11'), new_lhs])]
        case Collect(size):
            return [Instr('movq', [Reg('r15'), Reg('rdi')]),
                    Instr('movq', [self.select_arg(Constant(size)),
                                   Reg('rsi')]),
                    Callq('collect', 2)]
        case Assign([lhs], Subscript(tup, index, Load())):
            new_lhs = self.select_arg(lhs)
            new_tup = self.select_arg(tup)
            new_index = self.select_arg(index).value
            return [Instr('movq', [new_tup, Reg('r11')]),
                    Instr('movq', [Deref('r11', 8 * (new_index + 1)), new_lhs])]
        case Assign([Subscript(tup, index, Store())], rhs):
            new_tup = self.select_arg(tup)
            new_index = self.select_arg(index).value
            new_rhs = self.select_arg(rhs)
            return [Instr('movq', [new_tup, Reg('r11')]),
                    Instr('movq', [new_rhs, Deref('r11', 8*(new_index + 1))])]
        case Assign([lhs], Call(Name('len'), [tup])):
            new_lhs = self.select_arg(lhs)        
            new_tup = self.select_arg(tup)
            return [Instr('movq', [new_tup, Reg('rax')]),
                    Instr('movq', [Deref('rax', 0), Reg('rax')]),
                    Instr('andq', [Immediate(126), Reg('rax')]),
                    Instr('sarq', [Immediate(1), Reg('rax')]),
                    Instr('movq', [Reg('rax'), new_lhs])]
        case _:
            return super().select_stmt(s)

    def select_instructions(self, p: CProgram) -> X86Program:
        match p:
            case CProgram(body):
                blocks = {}
                for (l, ss) in body.items():
                    blocks[l] = sum([self.select_stmt(s) for s in ss], [])
                new_p = X86Program(blocks)
                new_p.var_types = p.var_types
                return new_p
  
    ###########################################################################
    # Uncover Live
    ###########################################################################

    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case Global(name):
                return set()
            case _:
                return super().vars_arg(a)

    ###########################################################################
    # Build Interference
    ###########################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(body):
                self.var_types = p.var_types
                return super().build_interference(p, live_after)

    def interfere_instr(self, i: instr, graph: UndirectedAdjList,
                        live_after: Dict[instr, Set[location]]):
        match i:
            case Callq(func, n) if func == 'collect':
                for v in live_after[i]:
                    if not (v.id in registers) and self.is_root_type(self.var_types[v.id]):
                        for u in callee_save_for_alloc:
                            graph.add_edge(Reg(u), v)
                super().interfere_instr(i, graph, live_after)
            case _:
                super().interfere_instr(i, graph, live_after)
                            
    ###########################################################################
    # Allocate Registers
    ###########################################################################

    def valid_color(self, c, v, unavail_colors):
        return (not (c in unavail_colors[v])) \
            and ((c < len(registers_for_alloc)) \
                 or (self.is_root_type(self.var_types[v.id]) and c%2 == 0) \
                 or (not self.is_root_type(self.var_types[v.id]) and c%2 == 1))
    
    def choose_color(self, v, unavail_colors):
        c = 0
        while not self.valid_color(c, v, unavail_colors):
            c += 1
        return c

    def identify_home(self, c: int, first_location: int) -> arg:
        n = len(registers_for_alloc)
        if c < n:
            return Reg(registers_for_alloc[c])
        elif c%2 == 0: # root stack
            new_c = floor((c - n) / 2)
            offset = - 8*(new_c + 1)
            return Deref('r15', offset)
        else:          # regular stack
            new_c = floor((c - n) / 2)
            trace("color: " + repr(c) + ", new color: " + repr(new_c) + "\n")
            offset = - (first_location + 8 * new_c)
            return Deref('rbp', offset)

    def alloc_reg_blocks(self, blocks,
                         graph: UndirectedAdjList,
                         var_types) -> X86Program:
        variables = set().union(*[self.collect_locals_instrs(ss) \
                                  for (l, ss) in blocks.items()])
        self.var_types = var_types
        trace('var_types:')
        trace(var_types)
        (color, spills) = self.color_graph(graph, variables)
        # trace('spills:')
        # trace(spills)
        # trace('color:')
        # trace(color)
        root_spills = set()
        stack_spills = set()
        for s in spills:
            if self.is_root_type(var_types[s.id]):
                root_spills = root_spills.union(set([s.id]))
            else:
                stack_spills = stack_spills.union(set([s.id]))
        used_callee = self.used_callee_reg(variables, color)
        num_callee = len(used_callee)
        home = {x: self.identify_home(color[x], 8 + 8 * num_callee) \
                for x in variables}
        trace('home:')
        trace(home)
        new_blocks = {l: self.assign_homes_instrs(ss, home) \
               for (l, ss) in blocks.items()}
        return (new_blocks, used_callee, num_callee, stack_spills, root_spills)
        
    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86Program(blocks):
                (new_blocks, used_callee, num_callee, stack_spills, root_spills) = \
                    self.alloc_reg_blocks(blocks, graph, p.var_types)
                new_p = X86Program(new_blocks)
                new_p.stack_space = \
                    align(8 * (num_callee + len(stack_spills)), 16) \
                    - 8 * num_callee
                new_p.used_callee = used_callee
                new_p.num_root_spills = len(root_spills)
                return new_p
            
    ############################################################################
    # Assign Homes
    ############################################################################
              
    def collect_locals_arg(self, a: arg) -> Set[location]:
        match a:
            case Global(name):
                return set()
            case _:
                return super().collect_locals_arg(a)

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case Global(name):
                return Global(name)
            case _:
                return super().assign_homes_arg(a, home)

    ############################################################################
    # Patch Instructions
    ############################################################################

    def in_memory(self, a: arg) -> bool:
        if isinstance(a, Global):
            return True
        else:
            return super().in_memory(a)
    
    def patch_instructions(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                blocks = {l: self.patch_instrs(ss) for (l, ss) in body.items()}
                new_p = X86Program(blocks)
                new_p.stack_space = p.stack_space
                new_p.used_callee = p.used_callee
                new_p.num_root_spills = p.num_root_spills
                return new_p
            
    ############################################################################
    # Prelude and Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                save_callee_reg = []
                for r in p.used_callee:
                    save_callee_reg.append(Instr('pushq', [Reg(r)]))
                restore_callee_reg = []
                for r in reversed(p.used_callee):
                    restore_callee_reg.append(Instr('popq', [Reg(r)]))
                rootstack_size = 2 ** 16
                #heap_size = 2 ** 16
                heap_size = 2 ** 4   # this size is good for revealing bugs
                initialize_heaps = \
                    [Instr('movq', [Immediate(rootstack_size), Reg('rdi')]), 
                     Instr('movq', [Immediate(heap_size), Reg('rsi')]),
                     Callq('initialize', 2),
                     Instr('movq', [Global('rootstack_begin'),
                                    Reg('r15')])]
                initialize_roots = []
                for i in range(0, p.num_root_spills):
                    initialize_roots += \
                        [Instr('movq', [Immediate(0), Deref('r15', 0)]),
                         Instr('addq', [Immediate(8), Reg('r15')])]
                main = [Instr('pushq', [Reg('rbp')]), \
                        Instr('movq', [Reg('rsp'), Reg('rbp')])] \
                        + save_callee_reg \
                        + [Instr('subq',[Immediate(p.stack_space),Reg('rsp')])]\
                        + initialize_heaps \
                        + initialize_roots \
                        + [Jump('start')]
                concl = [Instr('subq', [Immediate(8 * p.num_root_spills),
                                        Reg('r15')])] \
                      + [Instr('addq', [Immediate(p.stack_space),Reg('rsp')])] \
                      + restore_callee_reg \
                      + [Instr('popq', [Reg('rbp')]),
                         Instr('retq', [])]
                body['main'] = main
                body['conclusion'] = concl
                return X86Program(body)

    
typecheck_Ltup = type_check_Ltup.TypeCheckLtup().type_check
typecheck_Ctup = type_check_Ctup.TypeCheckCtup().type_check
typecheck_dict = {
    'source': typecheck_Ltup,
    'shrink': typecheck_Ltup,
    'expose_allocation': typecheck_Ltup,
    'remove_complex_operands': typecheck_Ltup,
    'explicate_control': typecheck_Ctup,
}
interpLtup = interp_Ltup.InterpLtup().interp
interpCtup = interp_Ctup.InterpCtup().interp
interp_dict = {
    'shrink': interpLtup,
    'expose_allocation': interpLtup,
    'remove_complex_operands': interpLtup,
    'explicate_control': interpCtup,
    #'select_instructions': racket_interp_pseudo_x86,
    #'assign_homes': racket_interp_x86,
    #'patch_instructions': racket_interp_x86,
}

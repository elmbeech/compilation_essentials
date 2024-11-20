# Language L_If
#
# Concrete Syntax
#
# exp ::= ... | exp `-` exp
#       | `True` | `False` | exp `if` exp `else` exp
#       | exp `and` exp | exp `or` exp | `not` exp
#       | exp `<` exp | exp `<=` exp | exp `>` exp | exp `>=` exp
#       | exp `==` exp | exp `!=` exp
# stmt ::= ... | `if` exp `:` stmt+ `else:` stmt+
# 
#
# Abstract Syntax
#
# boolop ::= And() | Or() |
# cmp ::= Lt() | LtE() | Gt() | GtE() | Eq() | NotEq()
# exp ::= ... | BinOp(exp, Sub(), exp)
#       | IfExp(exp,exp,exp)
#       | BoolOp(boolop, [exp, exp]) | UnaryOp(Not(), exp)
#       | Compare(exp, [cmp], [exp])
# stmt ::= ... | If(exp, [stmt], [stmt])

from ast import *
from utils import *
from x86_ast import *
from graph import UndirectedAdjList, DirectedAdjList, transpose, topological_sort
import var
from var import Temporaries
import register_allocator
from register_allocator import byte_to_full_reg
import sys
import os
from typing import List, Dict, Set, Tuple
import interp_Lif
import type_check_Lif
import interp_Cif
import type_check_Cif
from eval_x86 import interp_x86

class Conditionals(register_allocator.RegisterAllocator):

    ############################################################################
    # Shrink
    ############################################################################

    def shrink(self, p: Module) -> Module:
        match p:
            case Module(body):
                return Module([self.shrink_stmt(s) for s in body])

    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case Assign(targets, value):
                return Assign([self.shrink_exp(e) for e in targets],
                              self.shrink_exp(value))
            case Expr(value):
                return Expr(self.shrink_exp(value))
            case If(test, body, orelse):
                return If(self.shrink_exp(test),
                          [self.shrink_stmt(s) for s in body],
                          [self.shrink_stmt(s) for s in orelse])
            case _:
                raise Exception('shrink_stmt: unexpected: ' + repr(s))

    def shrink_exp(self, e: expr) -> expr:
        match e:
            case Name(id):
                return e
            case Constant(value):
                return e
            case BinOp(left, op, right):
                l = self.shrink_exp(left);
                r = self.shrink_exp(right)
                return BinOp(l, op, r)
            case UnaryOp(op, operand):
                rand = self.shrink_exp(operand)
                return UnaryOp(op, rand)
            case Call(func, args):
                fun = self.shrink_exp(func)
                new_args = [self.shrink_exp(arg) for arg in args]
                return Call(fun, new_args)
            case IfExp(test, body, orelse):
                tst = self.shrink_exp(test)
                bod = self.shrink_exp(body);
                els = self.shrink_exp(orelse)
                return IfExp(tst, bod, els)
            # Replace And with IfExp
            case BoolOp(And(), values):  # values was [left,right], bug? -Jeremy
                l = self.shrink_exp(values[0])
                r = self.shrink_exp(values[1])
                return IfExp(l, r, Constant(False))
            # Replace Or with IfExp
            case BoolOp(Or(), values):
                l = self.shrink_exp(values[0])
                r = self.shrink_exp(values[1])
                return IfExp(l, Constant(True), r)
            case Compare(left, [op], [right]):
                l = self.shrink_exp(left);
                r = self.shrink_exp(right)
                return Compare(l, [op], [r])
            case _:
                raise Exception('shrink_exp: ' + repr(e))

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case If(test, body, orelse):
                (test, bs) = self.rco_exp(test, False)
                sss1 = [self.rco_stmt(s) for s in body]
                sss2 = [self.rco_stmt(s) for s in orelse]
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] \
                       + [If(test, sum(sss1, []), sum(sss2, []))]
            case _:
                return super().rco_stmt(s)

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr,Temporaries]:
        match e:
            case IfExp(test, body, orelse):
                (new_test, bs1) = self.rco_exp(test, False)
                (new_body, bs2) = self.rco_exp(body, False)
                (new_orelse, bs3) = self.rco_exp(orelse, False)
                new_body = make_begin(bs2, new_body)
                new_orelse = make_begin(bs3, new_orelse)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return (tmp, bs1 + [(tmp, IfExp(new_test, new_body,
                                                    new_orelse))])
                else:
                    return IfExp(new_test, new_body, new_orelse), bs1
            case Compare(left, [op], [right]):
                (l, bs1) = self.rco_exp(left, True)
                (r, bs2) = self.rco_exp(right, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, bs1 + bs2 + [(tmp, Compare(l, [op], [r]))]
                else:
                    return Compare(l, [op], [r]), bs1 + bs2
            case _:
                return super().rco_exp(e, need_atomic)

    ############################################################################
    # Explicate Control
    ############################################################################

    def create_block(self, stmts: List[stmt],
                     basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match stmts:
          case [Goto(l)]:
            return stmts
          case _:
            label = generate_name('block')
            basic_blocks[label] = stmts
            return [Goto(label)]

    def explicate_effect(self, e: expr, cont: List[stmt],
                         basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Begin(body, result):
                ss = self.explicate_effect(result, cont, basic_blocks)
                for s in reversed(body):
                  ss = self.explicate_stmt(s, ss, basic_blocks)
                return ss
            case IfExp(test, body, orelse):
                goto = self.create_block(cont, basic_blocks)
                new_body = self.explicate_effect(body, goto, basic_blocks)
                new_orelse = self.explicate_effect(orelse, goto, basic_blocks)
                return self.explicate_pred(test, new_body, new_orelse,
                                           basic_blocks)
            case Call(func, args):
                return [Expr(e)] + cont
            case _:  # no effect, remove this expression
                return cont

    def explicate_assign(self, e: expr, x: Variable, cont: List[stmt],
                         basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Begin(body, result):
              ss = self.explicate_assign(result, x, cont, basic_blocks)
              for s in reversed(body):
                  ss = self.explicate_stmt(s, ss, basic_blocks)
              return ss
            case IfExp(test, body, orelse):
                goto = self.create_block(cont, basic_blocks)
                new_body = self.explicate_assign(body, x, goto, basic_blocks)
                new_orelse = self.explicate_assign(orelse, x, goto,
                                                   basic_blocks)
                return self.explicate_pred(test, new_body, new_orelse,
                                           basic_blocks)
            case _:
                return [Assign([x], e)] + cont
            
    def generic_explicate_pred(self, cnd: expr, thn: List[stmt],
                               els: List[stmt],
                               basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        return [If(Compare(cnd, [Eq()], [Constant(False)]),
                   self.create_block(els, basic_blocks),
                   self.create_block(thn, basic_blocks))]

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Name(x):
                return self.generic_explicate_pred(cnd, thn, els, basic_blocks)
            case Compare(left, [op], [right]):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                return [If(cnd, goto_thn, goto_els)]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case UnaryOp(Not(), operand):
                return self.explicate_pred(operand, els, thn, basic_blocks)
            case Begin(body, result):
              ss = self.explicate_pred(result, thn, els, basic_blocks)
              for s in reversed(body):
                  ss = self.explicate_stmt(s, ss, basic_blocks)
              return ss
            case IfExp(test, body, orelse):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                new_body = self.explicate_pred(body, goto_thn, goto_els,
                                               basic_blocks)
                new_els = self.explicate_pred(orelse, goto_thn, goto_els,
                                              basic_blocks)
                return self.explicate_pred(test, new_body, new_els,
                                           basic_blocks)
            case _:
                raise Exception('explicate_pred: unexpected ' + repr(cnd))

    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                goto = self.create_block(cont, basic_blocks)
                new_body = goto
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                new_els = goto
                for s in reversed(orelse):
                    new_els = self.explicate_stmt(s, new_els, basic_blocks)
                return self.explicate_pred(test, new_body, new_els,
                                           basic_blocks)
            case _:
                raise Exception('explicate_stmt: unexpected ' + repr(s))

    def explicate_control(self, p: Module) -> CProgram:
        match p:
            case Module(body):
                new_body = [Return(Constant(0))]
                basic_blocks = {}
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                basic_blocks['start'] = new_body
                return CProgram(basic_blocks)
            case _:
                raise Exception('explicate_control: unexpected ' + repr(p))

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, a: expr) -> arg:
        match a:
            case Constant(True):
                return Immediate(1)
            case Constant(False):
                return Immediate(0)
            case Reg(id):  # cause how we handle Return
                return Reg(id)
            case _:
                return super().select_arg(a)

    def select_instructions(self, p: CProgram) -> X86Program:
        match p:
            case CProgram(body):
                blocks = {}
                for (l, ss) in body.items():
                    blocks[l] = sum([self.select_stmt(s) for s in ss], [])
                return X86Program(blocks)

    def select_stmt(self, s: stmt) -> List[instr]:
        match s:
            case If(Compare(left, [op], [right]), [Goto(thn)], [Goto(els)]):
                l = self.select_arg(left)
                r = self.select_arg(right)
                return [Instr('cmpq', [r, l]),
                        JumpIf(self.select_op(op), thn),
                        Jump(els)]
            case Goto(label):
                return [Jump(label)]
            case Assign([lhs], UnaryOp(Not(), operand)):
                new_lhs = self.select_arg(lhs)
                new_operand = self.select_arg(operand)
                return ([Instr('movq', [new_operand, new_lhs])]
                        if new_lhs != new_operand else []) \
                    + [Instr('xorq', [Immediate(1), new_lhs])]
            case Assign([lhs], BinOp(left, Sub(), right)) if left == lhs:
                new_lhs = self.select_arg(lhs)
                r = self.select_arg(right)
                return [Instr('subq', [r, new_lhs])]
            case Assign([lhs], Compare(left, [op], [right])):
                new_lhs = self.select_arg(lhs)
                l = self.select_arg(left)
                r = self.select_arg(right)
                # in cmpq, the left and right get swapped. -Jeremy
                if isinstance(r, Immediate):
                    comparison = [Instr('movq', [l, Reg('rax')]),
                                  Instr('cmpq', [r, Reg('rax')])]
                else:
                    comparison = [Instr('cmpq', [r, l])]
                return comparison + \
                       [Instr('set' + self.select_op(op), [ByteReg('al')]),
                        Instr('movzbq', [ByteReg('al'), new_lhs])]
            case Return(value):
                ins = self.select_stmt(Assign([Reg('rax')], value))
                return ins + [Jump('conclusion')]
            case _:
                return super().select_stmt(s)

    def select_op(self, op: operator) -> str:
        match op:
            case Sub():
                return 'subq'
            case And():
                return 'andq'
            case Eq():
                return 'e'
            case NotEq():
                return 'ne'
            case Lt():
                return 'l'
            case LtE():
                return 'le'
            case Gt():
                return 'g'
            case GtE():
                return 'ge'
            case _:
                return super().select_op(op)

    ############################################################################
    # Uncover Live
    ############################################################################

    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case ByteReg(id):
                return {Reg(byte_to_full_reg[id])}
            case _:
                return super().vars_arg(a)

    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Jump(label):
                return set()
            case JumpIf(cc, label):
                return set()
            case _:
                return super().read_vars(i)

    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case Jump(label):
                return set()
            case JumpIf(cc, label):
                return set()
            case Instr('cmpq', args):
                return {Reg('__flag')}
            case _:
                return super().write_vars(i)

    @staticmethod
    def adjacent_instr(s: instr) -> List[str]:
        if isinstance(s, Jump) or isinstance(s, JumpIf):
            return [s.label]
        else:
            return []

    def blocks_to_graph(self,
                        blocks: Dict[str, List[instr]]) -> DirectedAdjList:
        graph = DirectedAdjList()
        for u in blocks.keys():
            graph.add_vertex(u)
        for (u, ss) in blocks.items():
            for s in ss:
                for v in self.adjacent_instr(s):
                    graph.add_edge(u, v)
        return graph

    def trace_live_blocks(self, blocks, live_before: Dict[instr, Set[location]],
                   live_after: Dict[instr, Set[location]]):
        for (l, ss) in blocks.items():
            trace(l + ':\n')
            i = 0 
            for s in ss:
                if i == 0:
                    trace('\t\t{' + ', '.join([str(l) for l in live_before[s]]) + '}')
                trace(str(s))
                trace('\t\t{' + ', '.join([str(l) for l in live_after[s]]) + '}')
                i = i + 1
                
    def trace_live(self, p: X86Program, live_before: Dict[instr, Set[location]],
                   live_after: Dict[instr, Set[location]]):
        match p:
            case X86Program(body):
                self.trace_live_blocks(body, live_before, live_after)
                
    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(body):
                live_before = {}
                live_after = {}
                cfg = self.blocks_to_graph(body)
                cfg_trans = transpose(cfg)
                live_before_block = \
                    {'conclusion': {Reg('rax'), Reg('rsp')}}
                for l in topological_sort(cfg_trans):
                    if l != 'conclusion':
                        adj_live = [live_before_block[v] \
                                    for v in cfg.adjacent(l)]
                        live_before_succ = set().union(*adj_live)
                        for i in reversed(body[l]):
                            self.uncover_live_instr(i, live_before_succ,
                                                    live_before, live_after)
                            live_before_succ = live_before[i]
                        live_before_block[l] = live_before_succ
                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after


    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference_blocks(self, blocks,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        graph = UndirectedAdjList()
        for (l, ss) in blocks.items():
            for i in ss:
                self.interfere_instr(i, graph, live_after)
        return graph
        
    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(blocks):
                return self.build_interference_blocks(blocks, live_after)

    def interfere_instr(self, i: instr, graph,
                        live_after: Dict[instr, Set[location]]):
        match i:
            case Instr('movzbq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)
            case _:
                return super().interfere_instr(i, graph, live_after)

    ############################################################################
    # Allocate Registers
    ############################################################################

    def alloc_reg_blocks(self, blocks,
                         graph: UndirectedAdjList) -> X86Program:
        variables = set().union(*[self.collect_locals_instrs(ss) \
                                  for (l, ss) in blocks.items()])
        (color, spills) = self.color_graph(graph, variables)
        used_callee = self.used_callee_reg(variables, color)
        num_callee = len(used_callee)
        home = {x: self.identify_home(color[x], 8 + 8 * num_callee) \
                for x in variables}
        new_blocks = {l: self.assign_homes_instrs(ss, home) \
               for (l, ss) in blocks.items()}
        return (new_blocks, used_callee, num_callee, spills)
    
    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86Program(blocks):
                (new_blocks, used_callee, num_callee, spills) = \
                    self.alloc_reg_blocks(blocks, graph)
                new_p = X86Program(new_blocks)
                new_p.stack_space = align(8 * (num_callee + len(spills)), 16) \
                                    - 8 * num_callee
                new_p.used_callee = used_callee
                return new_p

    ############################################################################
    # Assign Homes
    ############################################################################

    def collect_locals_instr(self, i: instr) -> Set[location]:
        match i:
            case JumpIf(cc, label):
                return set()
            case Jump(label):
                return set()
            case _:
                return super().collect_locals_instr(i)

    def collect_locals_arg(self, a: arg) -> Set[location]:
        match a:
            case ByteReg(id):
                return set()
            case _:
                return super().collect_locals_arg(a)

    def assign_homes_instr(self, i: instr, home: Dict[location, arg]) -> instr:
        match i:
            case JumpIf(cc, label):
                return i
            case Jump(label):
                return i
            case _:
                return super().assign_homes_instr(i, home)

    def assign_homes_arg(self, a: arg, home: Dict[location, arg]) -> arg:
        match a:
            case ByteReg(id):
                return a
            case _:
                return super().assign_homes_arg(a, home)

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instructions(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                blocks = {l: self.patch_instrs(ss) for (l, ss) in body.items()}
                new_p = X86Program(blocks)
                new_p.stack_space = p.stack_space
                new_p.used_callee = p.used_callee
                return new_p

    def patch_instr(self, i: instr) -> List[instr]:
        match i:
            case JumpIf(cc, label):
                return [i]
            case Jump(label):
                return [i]
            case Instr('cmpq', [left, Immediate(v)]):
                return [Instr('movq', [Immediate(v), Reg('rax')]),
                        Instr('cmpq', [left, Reg('rax')])]

            case Instr('cmpq', [left, right]) if (self.in_memory(left) \
                                                  and self.in_memory(right)):
                return [Instr('movq', [right, Reg('rax')]),
                        Instr('cmpq', [left, Reg('rax')])]
            case Instr('movzbq', [s, t]) if self.in_memory(t):
                return [Instr('movzbq', [s, Reg('rax')]),
                        Instr('movq', [Reg('rax'), t])]
            case _:
                return super().patch_instr(i)

    ############################################################################
    # Prelude & Conclusion
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
                main = [Instr('pushq', [Reg('rbp')]), \
                        Instr('movq', [Reg('rsp'), Reg('rbp')])] \
                       + save_callee_reg \
                       + [Instr('subq', [Immediate(p.stack_space),Reg('rsp')]),\
                          Jump('start')]
                concl = [Instr('addq', [Immediate(p.stack_space),Reg('rsp')])] \
                        + restore_callee_reg \
                        + [Instr('popq', [Reg('rbp')]),
                           Instr('retq', [])]
                body['main'] = main
                body['conclusion'] = concl
                return X86Program(body)


typecheck_Lif = type_check_Lif.TypeCheckLif().type_check
typecheck_Cif = type_check_Cif.TypeCheckCif().type_check
typecheck_dict = {
    'source': typecheck_Lif,
    'shrink': typecheck_Lif,
    'uniquify': typecheck_Lif,
    'remove_complex_operands': typecheck_Lif,
    'explicate_control': typecheck_Cif,
}
interpLif = interp_Lif.InterpLif().interp
interpCif = interp_Cif.InterpCif().interp
interp_dict = {
    'shrink': interpLif,
    'uniquify': interpLif,
    'remove_complex_operands': interpLif,
    'explicate_control': interpCif,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

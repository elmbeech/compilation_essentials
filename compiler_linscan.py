# willem armentrout
# elmar bucher

# Language P_var
#
# Concrete Syntax
#
# exp ::= var | int | `input_int` `(` `)` | `-` exp | exp `+` exp
# stmt ::= var `=` exp | `print` `(` exp `)` | exp
# program ::= stmt+
#
#
# Abstract Syntax
#
# exp ::= Name(var) | Constant(int) | Call(Name('input_int'), [])
#       | UnaryOp(USub(), exp) | BinOp(exp, Add(), exp)
# stmt ::= Assign([var],exp) | Expr(Call(Name('print'), [exp])) | Expr(exp)
# program ::= Module([stmt])

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

# Language L_While
#
# Concrete Syntax
#
# stmt ::= ... | `while` exp `:` stmt+
#
# Abstract Syntax
#
#  stmt ::= ... | While(exp, stmt+, [])


# library

#import ast
from ast import *
from dataflow_analysis import analyze_dataflow
from graph import UndirectedAdjList, DirectedAdjList, transpose, topological_sort
import interp_Lvar
import interp_Lif
import interp_Cif
import interp_Lwhile
import interp_Ltup
import interp_Ctup
from interp_x86.eval_x86 import interp_x86
from racket_interp_x86 import *
from math import floor
from priority_queue import PriorityQueue
import type_check_Lvar
import type_check_Lif
import type_check_Cif
import type_check_Lwhile
import type_check_Cwhile
import type_check_Ltup
import type_check_Ctup
from utils import *
from x86_ast import *


# types

import typing
from typing import List, Set, Dict  # Tuple causes troubles!
Binding = tuple[Name, expr]
Temporaries = List[Binding]


# const

caller_save: Set[str] = {'rax', 'rcx', 'rdx', 'rsi', 'rdi', 'r8', 'r9', 'r10', 'r11'}
callee_save: Set[str] = {'rsp', 'rbp', 'rbx', 'r12', 'r13', 'r14', 'r15'}
reserved_registers: Set[str] = {'rax', 'r11', 'r15', 'rsp', 'rbp', '__flag'}
general_registers: List[str] = ['rcx', 'rdx', 'rsi', 'rdi', 'r8', 'r9', 'r10',
                     'rbx', 'r12', 'r13', 'r14']
registers_for_alloc: List[str] = general_registers
# registers_for_alloc = ['rcx','rbx']
# registers_for_alloc = ['rdi','rcx','rbx']
arg_registers: List[str] = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']
registers = set(general_registers).union(reserved_registers)

caller_save_for_alloc = caller_save.difference(reserved_registers) \
                                   .intersection(set(registers_for_alloc))
callee_save_for_alloc = callee_save.difference(reserved_registers) \
                                   .intersection(set(registers_for_alloc))

byte_to_full_reg = \
    {'ah': 'rax', 'al': 'rax',
     'bh': 'rbx', 'bl': 'rbx',
     'ch': 'rcx', 'cl': 'rcx',
     'dh': 'rdx', 'dl': 'rdx'}

register_color = {'rax': -1, 'rsp': -2, 'rbp': -3, 'r11': -4, 'r15': -5, '__flag': -6}

for i, r in enumerate(registers_for_alloc):
    register_color[r] = i

extra_arg_registers = list(set(arg_registers) - set(registers_for_alloc))
for i, r in enumerate(extra_arg_registers):
    register_color[r] = -i - 6


# class and fucntions

class Var:

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr, Temporaries]:
        match e:
            case Name(id):
                return e, []

            case Constant(value):
                if need_atomic and self.big_constant(e):
                    tmp = Name(generate_name('tmp'))
                    return tmp, [(tmp, Constant(value))]
                else:
                    return e, []

            case BinOp(left, op, right):
                (l, bs1) = self.rco_exp(left, True)
                (r, bs2) = self.rco_exp(right, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    b = BinOp(l, op, r)
                    return tmp, bs1 + bs2 + [(tmp, b)]
                else:
                    return BinOp(l, op, r), bs1 + bs2

            # needed for tests/int64/min-int.py
            case UnaryOp(USub(), Constant(value)):
              return self.rco_exp(Constant(-value), need_atomic)

            case UnaryOp(op, operand):
                (rand, bs) = self.rco_exp(operand, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, bs + [(tmp, UnaryOp(op, rand))]
                else:
                    return UnaryOp(op, rand), bs

            case Call(func, args):
                (new_func, bs1) = self.rco_exp(func, True)
                (new_args, bss2) = \
                    unzip([self.rco_exp(arg, True) for arg in args])
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return (tmp, bs1 + sum(bss2, [])
                            + [(tmp, Call(new_func, new_args, []))])
                else:
                    return Call(new_func, new_args, []), bs1 + sum(bss2, [])
            case _:
                raise Exception('error in rco_exp, unhandled: ' + repr(e))

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Assign(targets, value):
                new_value, bs = self.rco_exp(value, False)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] \
                    + [Assign(targets, new_value)]
            case Expr(value):
                new_value, bs = self.rco_exp(value, False)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] \
                    + [Expr(new_value)]
            case _:
                raise Exception('error in rco_stmt, unhandled: ' + repr(s))

    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(body):
                sss = [self.rco_stmt(s) for s in body]
                return Module(sum(sss, []))
            case _:
                raise Exception('error remove_complex_operators, unhandled: '\
                                + repr(p))

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        match e:
            case Name(id):
                return Variable(id)
            case Constant(value):
                return Immediate(value)
            case _:
                raise Exception('select_arg unhandled: ' + repr(e))

    def select_op(self, op: operator) -> str:
        match op:
            case Add():
                return 'addq'
            case Sub():
                return 'subq'
            case USub():
                return 'negq'
            case _:
                raise Exception('select_op unhandled: ' + repr(op))

    def select_stmt(self, s: stmt) -> List[instr]:
        match s:
            case Expr(Call(Name('input_int'), [])):
                return [Callq('read_int', 0)]
            case Expr(Call(Name('print'), [operand])):
                return [Instr('movq', [self.select_arg(operand), Reg('rdi')]),
                        Callq('print_int', 1)]
            case Expr(value):
                return []
            case Assign([lhs], Name(id)):
                new_lhs = self.select_arg(lhs)
                if Name(id) != lhs:
                    return [Instr('movq', [Variable(id), new_lhs])]
                else:
                    return []
            case Assign([lhs], Constant(value)):
                new_lhs = self.select_arg(lhs)
                rhs = self.select_arg(Constant(value))
                return [Instr('movq', [rhs, new_lhs])]
            case Assign([lhs], UnaryOp(USub(), Constant(i))):
                new_lhs = self.select_arg(lhs)
                # not just an optimization; needed to handle min-int
                return [Instr('movq',[Immediate(neg64(i)),new_lhs])]
            case Assign([lhs], UnaryOp(op, operand)):
                new_lhs = self.select_arg(lhs)
                rand = self.select_arg(operand)
                return [Instr('movq', [rand, new_lhs]),
                        Instr(self.select_op(op), [new_lhs])]
            case Assign([lhs], BinOp(left, Add(), right)) if left == lhs:
                new_lhs = self.select_arg(lhs)
                r = self.select_arg(right)
                return [Instr('addq', [r, new_lhs])]
            case Assign([lhs], BinOp(left, Add(), right)) if right == lhs:
                new_lhs = self.select_arg(lhs)
                l = self.select_arg(left)
                return [Instr('addq', [l, new_lhs])]
            case Assign([lhs], BinOp(left, Sub(), right)) if right == lhs:
                new_lhs = self.select_arg(lhs)
                l = self.select_arg(left)
                # why not use subq?
                return [Instr('negq', [new_lhs]),
                        Instr('addq', [l, new_lhs])]
            case Assign([lhs], BinOp(left, op, right)):
                new_lhs = self.select_arg(lhs)
                l = self.select_arg(left)
                r = self.select_arg(right)
                return [Instr('movq', [l, new_lhs]),
                        Instr(self.select_op(op), [r, new_lhs])]
            case Assign([lhs], Call(Name('input_int'), [])):
                new_lhs = self.select_arg(lhs)
                return [Callq('read_int', 0),
                        Instr('movq', [Reg('rax'), new_lhs])]
            case Assign([lhs], Call(Name('print'), [operand])):
                return [Instr('movq', [self.select_arg(operand), Reg('rdi')]),
                        Callq('print_int', 1)]
            case _:
                raise Exception('error in select_stmt, unknown: ' + repr(s))

    def select_instructions(self, p: Module) -> X86Program:
        match p:
            case Module(body):
                sss = [self.select_stmt(s) for s in body]
                return X86Program(sum(sss, []))

    ############################################################################
    # Assign Homes
    ############################################################################

    def collect_locals_instr(self, i: instr) -> Set[location]:
        match i:
            case Instr(inst, args):
                lss = [self.collect_locals_arg(a) for a in args]
                return set().union(*lss)
            case Callq(func, num_args):
                return set()
            case _:
                raise Exception('error in collect_locals_instr, unknown: ' + repr(i))

    def collect_locals_arg(self, a: arg) -> Set[location]:
        match a:
            case Reg(id):
                return set()
            case Variable(id):
                return {Variable(id)}
            case Immediate(value):
                return set()
            case Deref(reg, offset):
                return set()
            case _:
                raise Exception('error in collect_locals_arg, unknown: ' + repr(a))

    def collect_locals_instrs(self, ss: List[stmt]) -> Set[location]:
        return set().union(*[self.collect_locals_instr(s) for s in ss])

    @staticmethod
    def gen_stack_access(i: int) -> arg:
        return Deref('rbp', -(8 + 8 * i))

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case Reg(id):
                return a
            case Variable(id):
                return home.get(a, a)
            case Immediate(value):
                return a
            case Deref(reg, offset):
                return Deref(reg, offset)
            case _:
                raise Exception('error in assign_homes_arg, unknown: ' + repr(a))

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        match i:
            case Instr(instr, args):
                new_args = [self.assign_homes_arg(a, home) for a in args]
                return Instr(instr, new_args)
            case Callq(func, num_args):
                return i
            case _:
                raise Exception('assign_homes_instr, unexpected: ' + repr(i))

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[Variable, arg]) -> List[instr]:
        return [self.assign_homes_instr(s, home) for s in ss]

    def assign_homes(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                variables = self.collect_locals_instrs(body)
                home = {}
                for i, x in enumerate(variables):
                    home[x] = self.gen_stack_access(i)
                body = self.assign_homes_instrs(body, home)
                p = X86Program(body)
                p.stack_space = align(8 * len(variables), 16)
                return p

    ############################################################################
    # Patch Instructions
    ############################################################################

    @staticmethod
    def big_constant(c: arg) -> bool:
        return (isinstance(c, Immediate) or isinstance(c, Constant)) \
            and (c.value > (2 ** 16) or c.value < - (2 ** 16))

    def in_memory(self, a: arg) -> bool:
        return isinstance(a, Deref)

    def patch_instr(self, i: instr) -> List[instr]:
        match i:
            case Instr('movq', [s, t]):
                if (self.in_memory(s) or self.big_constant(s)) \
                       and self.in_memory(t):
                    return [Instr('movq', [s, Reg('rax')]),
                            Instr('movq', [Reg('rax'), t])]
                else:
                    return [i]
            case Instr(inst, [s, t]) \
                if (self.in_memory(s) and self.in_memory(t)) \
                   or self.big_constant(s):
                return [Instr('movq', [s, Reg('rax')]),
                        Instr(inst, [Reg('rax'), t])]
            case _:
                return [i]

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        return sum([self.patch_instr(i) for i in ss], [])

    def patch_instructions(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                new_p = X86Program(self.patch_instrs(body))
                new_p.stack_space = p.stack_space
                return new_p

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                prelude = [Instr('pushq', [Reg('rbp')]),
                           Instr('movq', [Reg('rsp'), Reg('rbp')]),
                           Instr('subq', [Immediate(p.stack_space),Reg('rsp')])]
                concl = [Instr('addq', [Immediate(p.stack_space),Reg('rsp')]),
                         Instr('popq', [Reg('rbp')]),
                         Instr('retq', [])]
                return X86Program(prelude + body + concl)



class RegisterAllocator(Var):

    ###########################################################################
    # Uncover Live
    ###########################################################################

    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case Variable(id):
                return {a}
            case Reg(id):
                return {a}
            case Deref(reg, offset):     # don't need this case
                return {Reg(reg)}      # problem for write?
            case Immediate(value):
                return set()
            case _:
                raise Exception('error in vars_arg, unhandled: ' + repr(a))

    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr('movq', [s, t]):
                return self.vars_arg(s)
            case Instr(instr, args):
                return set().union(*[self.vars_arg(arg) for arg in args])
            case Callq(func, num_args): # what if num_args > len(arg_registers)??
                return set([Reg(r) for r in arg_registers[0:num_args]])
            case _:
                raise Exception('error in read_vars, unexpected: ' + repr(i))

    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr(instr, [t]):
                return self.vars_arg(t)
            case Instr('cmpq', [s1, s2]):
                return set()
            case Instr(instr, [s, t]):
                return self.vars_arg(t)
            case Callq(func, num_args):
                return set([Reg(r) for r in caller_save_for_alloc])
            case _:
                raise Exception('error in write_vars, unexpected: ' + repr(i))

    def uncover_live_instr(self, i: instr, live_before_succ: Set[location],
                           live_before: Dict[instr, Set[location]],
                           live_after: Dict[instr, Set[location]]):
        live_after[i] = live_before_succ
        live_before[i] = live_after[i].difference(self.write_vars(i)) \
                                      .union(self.read_vars(i))

    def trace_live(self, p: X86Program, live_before: Dict[instr, Set[location]],
                   live_after: Dict[instr, Set[location]]):
        match p:
          case X86Program(body):
            i = 0
            for s in body:
                if i == 0:
                    trace('\t' + str(live_before[s]))
                trace(str(s))
                trace('\t' + str(live_after[s]))
                i = i + 1
            trace("")

    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(body):
                live_before = {}
                live_after = {}
                live_before_succ = set([])
                for i in reversed(body):
                    self.uncover_live_instr(i, live_before_succ, live_before,
                                            live_after)
                    live_before_succ = live_before[i]

                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after

    ###########################################################################
    # Build Interference
    ###########################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(body):
                G = UndirectedAdjList()
                for i in body:
                    self.interfere_instr(i, G, live_after)
                return G

    def interfere_instr(self, i: instr, graph: UndirectedAdjList,
                        live_after: Dict[instr, Set[location]]):
        match i:
            case Instr('movq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)
            case _:
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d:
                            graph.add_edge(d, v)

    ###########################################################################
    # Allocate Registers
    ###########################################################################

    def choose_color(self, v, unavail_colors):
        i = 0
        while i in unavail_colors[v]:
            i += 1
        return i

    # O(n * n * log(n))
    def color_graph(self, graph: UndirectedAdjList,
                    variables: Set[location]) -> tuple[Dict[location, int], Set[location]]:
        spills = set()
        unavail_colors = {}
        def compare(u, v):
            return len(unavail_colors[u.key]) < len(unavail_colors[v.key])
        Q = PriorityQueue(compare)
        color = {}
        for r in registers_for_alloc:
            color[Reg(r)] = register_color[r]
        for x in variables: # O(n log n), no its O(n * n)
            adj_reg = [y for y in graph.adjacent(x) if y.id in registers]
            unavail_colors[x] = \
                set().union([register_color[r.id] for r in adj_reg])
            Q.push(x) # O(log n)
        while not Q.empty():  # n iterations
            v = Q.pop() # O(log n)
            c = self.choose_color(v, unavail_colors)
            color[v] = c
            if c >= len(registers_for_alloc):
                spills = spills.union(set([v]))  # add method instead?
            for u in graph.adjacent(v): # n iterations
                if u.id not in registers: # use match on u instead?
                    unavail_colors[u].add(c)
                    Q.increase_key(u)  # log(n)
        return color, spills

    def identify_home(self, c: int, first_location: int) -> arg:
        if c < len(registers_for_alloc):
            return Reg(registers_for_alloc[c])
        else:
            offset = first_location + 8 * (c - len(registers_for_alloc))
            return Deref('rbp', - offset)

    def is_callee_color(self, c: int) -> bool:
        return c < len(registers_for_alloc) \
            and registers_for_alloc[c] in callee_save

    def used_callee_reg(self, variables: Set[location],
                        color: Dict[location, int]) -> Set[str]:
        result = set()
        for x in variables:
            if self.is_callee_color(color[x]):
                result.add(registers_for_alloc[color[x]])
        return list(result)

    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86Program(body):
                variables = self.collect_locals_instrs(body)
                (color, spills) = self.color_graph(graph, variables)
                trace("color")
                trace(color)
                trace("")
                used_callee = self.used_callee_reg(variables, color)
                num_callee = len(used_callee)
                home = {}
                for x in variables:
                    home[x] = self.identify_home(color[x], 8 + 8 * num_callee)
                trace("home")
                trace(home)
                trace("")
                new_body = [self.assign_homes_instr(s, home) for s in body]
                new_p = X86Program(new_body)
                new_p.stack_space = align(8 * (num_callee + len(spills)), 16) \
                    - 8 * num_callee
                new_p.used_callee = used_callee
                return new_p

    def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
        live_after = self.uncover_live(pseudo_x86)
        graph = self.build_interference(pseudo_x86, live_after)
        #trace(graph.show().source)
        trace("")
        return self.allocate_registers(pseudo_x86, graph)

    ###########################################################################
    # Patch Instructions
    ###########################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        match i:
            case Instr('movq', [s, t]) if s == t:
                return []
            case _:
                return super().patch_instr(i)

    def patch_instructions(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                new_p = X86Program(self.patch_instrs(body))
                new_p.stack_space = p.stack_space
                new_p.used_callee = p.used_callee
                return new_p

    ###########################################################################
    # Prelude & Conclusion
    ###########################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                save_callee_reg = []
                for r in p.used_callee:
                    save_callee_reg.append(Instr('pushq', [Reg(r)]))
                restore_callee_reg = []
                for r in reversed(p.used_callee):
                    restore_callee_reg.append(Instr('popq', [Reg(r)]))
                prelude = [Instr('pushq', [Reg('rbp')]), \
                        Instr('movq', [Reg('rsp'), Reg('rbp')])] \
                       + save_callee_reg \
                       + [Instr('subq', [Immediate(p.stack_space),Reg('rsp')])]
                concl = [Instr('addq', [Immediate(p.stack_space),Reg('rsp')])] \
                        + restore_callee_reg \
                        + [Instr('popq', [Reg('rbp')]),
                           Instr('retq', [])]
                return X86Program(prelude + body + concl)



class Conditionals(RegisterAllocator):

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

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr,Temporaries]:
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



class WhileLoops(Conditionals):

    ############################################################################
    # Shrink
    ############################################################################

    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case While(test, body, []):
                return While(self.shrink_exp(test),
                             [self.shrink_stmt(s) for s in body],
                             [])
            case _:
                return super().shrink_stmt(s)

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case While(test, body, []):
                (test, bs) = self.rco_exp(test, False)
                sss1 = [self.rco_stmt(s) for s in body]
                return [While(make_begin(bs, test), sum(sss1, []), [])]
            case _:
                return super().rco_stmt(s)

    ############################################################################
    # Explicate Control
    ############################################################################

    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case While(test, body, []):
                label = generate_name('loop')
                new_body = [Goto(label)]
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, blocks)
                loop = self.explicate_pred(test, new_body, cont, blocks)
                blocks[label] = loop
                return [Goto(label)]
            case _:
                return super().explicate_stmt(s, cont, blocks)

    ############################################################################
    # Uncover Live
    ############################################################################

    def uncover_live_block(self, label : str,
                           ss : List[stmt],
                           live : Set[location],
                           live_before : Dict[instr, Set[location]],
                           live_after : Dict[instr, Set[location]]) -> Set[location]:
        for i in reversed(ss):
            self.uncover_live_instr(i, live, live_before, live_after)
            live = live_before[i]
        return live

    # This is a method so it can be overridden (e.g. in functions.py)
    def liveness_transfer(self, blocks : Dict[str, List[instr]],
                          cfg : DirectedAdjList,
                          live_before : Dict[instr, Set[location]],
                          live_after : Dict[instr, Set[location]]) -> Set[location]:
        def live_xfer(label, live_before_succ):
            if label == 'conclusion':
                return {Reg('rax'), Reg('rsp')}
            else:
                return self.uncover_live_block(label, blocks[label], live_before_succ,
                                               live_before, live_after)
        return live_xfer

    def uncover_live_blocks(self, blocks):
        live_before = {}
        live_after = {}
        cfg = self.blocks_to_graph(blocks)
        transfer = self.liveness_transfer(blocks, cfg, live_before, live_after)
        bottom = set()
        join = lambda s, t: s.union(t)
        # liveness is a backward analysis, so we transpose the CFG
        analyze_dataflow(transpose(cfg), transfer, bottom, join)
        return live_before, live_after

    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(blocks):
                (live_before, live_after) = self.uncover_live_blocks(blocks)
                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after



class Tuples(WhileLoops):

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



class Compiler(Tuples):
    pass



# type checking

typecheck_Lvar = type_check_Lvar.TypeCheckLvar().type_check
typecheck_dict = {
    'source': typecheck_Lvar,
    'partial_eval': typecheck_Lvar,
    'remove_complex_operands': typecheck_Lvar,
}
interpLvar = interp_Lvar.InterpLvar().interp
interp_dict = {
    'partial_eval': interpLvar,
    'remove_complex_operands': interpLvar,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

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

typecheck_Lwhile = type_check_Lwhile.TypeCheckLwhile().type_check
typecheck_Cwhile = type_check_Cwhile.TypeCheckCwhile().type_check
typecheck_dict = {
    'source': typecheck_Lwhile,
    'shrink': typecheck_Lwhile,
    'expose_allocation': typecheck_Lwhile,
    'remove_complex_operands': typecheck_Lwhile,
    'explicate_control': typecheck_Cwhile,
}
interpLwhile = interp_Lwhile.InterpLwhile().interp
interpCwhile = interp_Cif.InterpCif().interp
interp_dict = {
    'shrink': interpLwhile,
    'expose_allocation': interpLwhile,
    'remove_complex_operands': interpLwhile,
    'explicate_control': interpCwhile,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

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


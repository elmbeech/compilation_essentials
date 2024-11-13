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
# stmt ::= ... | While(exp, stmt+ , [])
#
#
# Abstract Syntax
#
# stmt ::= ... | while exp: stmt+


# python standard libraries
import ast
from ast import *  # Tuple
from functools import reduce
import os
import sys

# essentials of compilation libraries
from graph import UndirectedAdjList, DirectedAdjList, transpose, topological_sort, deque
from priority_queue import PriorityQueue
from utils import *
from x86_ast import *


# const and type declaration
from typing import List, Dict, Set  #,Tuple bue 2024-10-30: overloads Tuple from ast!

Binding = tuple[Name, expr]
Temporaries = List[Binding]

caller_save: Set[str] = {'rax', 'rcx', 'rdx', 'rsi', 'rdi', 'r8', 'r9', 'r10', 'r11'}
callee_save: Set[str] = {'rsp', 'rbp', 'rbx', 'r12', 'r13', 'r14', 'r15'}
reserved_registers: Set[str] = {'rax', 'r11', 'r15', 'rsp', 'rbp', '__flag'}
general_registers: List[str] = ['rcx', 'rdx', 'rsi', 'rdi', 'r8', 'r9', 'r10', 'rbx', 'r12', 'r13', 'r14']
odd_registers: List[str] = ['r9', 'r11', 'r13']
even_registers: List[str] = ['r8', 'r10', 'r12', 'r14']
registers_for_alloc: List[str] = general_registers
# registers_for_alloc = ['rcx','rbx']
# registers_for_alloc = ['rdi','rcx','rbx']
arg_registers: List[str] = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']

registers = set(general_registers).union(reserved_registers)

caller_save_for_alloc = caller_save.difference(reserved_registers).intersection(set(registers_for_alloc))
callee_save_for_alloc = callee_save.difference(reserved_registers).intersection(set(registers_for_alloc))

byte_to_full_reg = {
    'ah':'rax', 'al':'rax',
    'bh':'rbx', 'bl':'rbx',
    'ch':'rcx', 'cl':'rcx',
    'dh':'rdx', 'dl':'rdx'
}

register_color = {'rax': -1, 'rsp': -2, 'rbp': -3, 'r11': -4, 'r15': -5, '__flag': -6}

for i, r in enumerate(registers_for_alloc):
    register_color[r] = i

extra_arg_registers = list(set(arg_registers) - set(registers_for_alloc))
for i, r in enumerate(extra_arg_registers):
    register_color[r] = -i - 6


# functions
class Compiler:

    ############################################################################
    # Shrink
    ############################################################################

    def shrink_exp(self, e: expr) -> expr:
        match e:
            case Name(var):
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

            case Tuple(exps, load):  # bue 20241030 load: https://docs.python.org/3/library/ast.html#ast.Load
                new_exps = [self.shrink_exp(exp) for exp in exps]
                return Tuple(new_exps, load)

            case Subscript(exp, const, load):
               new_exp = self.shrink_exp(exp)
               new_const = self.shrink_exp(const)
               return Subscript(new_exp, new_const, load)

            case _:
                raise Exception('error shrink_exp, unhandled: ' + repr(e))


    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case Assign(targets, value):
                return Assign([self.shrink_exp(e) for e in targets], self.shrink_exp(value))

            case Expr(value):
                return Expr(self.shrink_exp(value))

            case If(test, body, orelse):
                return If(self.shrink_exp(test),
                          [self.shrink_stmt(s) for s in body],
                          [self.shrink_stmt(s) for s in orelse])

            case While(cmp, body, []):
                return While(
                    self.shrink_exp(cmp),
                    [self.shrink_stmt(s) for s in body],
                    [])

            case _:
                raise Exception('shrink_stmt: unexpected: ' + repr(s))


    def shrink(self, p: Module) -> Module:
        match p:
            case Module(body):
                return Module([self.shrink_stmt(s) for s in body])


    ############################################################################
    # Expose Allocation Ltup -> Lalloc
    ############################################################################
    def ealloc_tuple(self, exps, type_tup):
        # if  tuple in tuple, half way initialized variables could be garbage collected
        # readinhg from a variable (stack) is save.

        # calculate memory needed
        i_word = len(exps)
        i_byte = i_word * 8 + 8 # bue 20241111: space at front of the 64 bit tag p109
        # temp var
        new_var = [Assign([Name(generate_name('init'))], self.ealloc_exp(exp)) for exp in exps]
        # conditional garbage collection
        new_garbage = [If(Compare(BinOp(GlobalValue('free_ptr'), Add(), Constant(i_byte)), [Lt()], [GlobalValue('fromspace_end')]), [Expr(Constant(0))], [Collect(i_byte)])]
        # allocate memory allication
        s_alloc = generate_name('alloc')
        new_memory = [Assign([Name(s_alloc)], Allocate(i_word, type_tup))]
        # initialize memory
        new_init = [Assign([Subscript(Name(s_alloc), Constant(n), Store())], var.targets[0]) for n, var in enumerate(new_var)]
        # output
        new_begin = Begin(new_var + new_garbage + new_memory + new_init, Name(s_alloc))
        return new_begin


    def ealloc_exp(self, e: expr):  #-> tuple[expr,Temporaries]:
        match e:
            case Begin(exprs):
               return e

            case BinOp(left, operator, right):
                new_left = self.ealloc_exp(left)
                new_right = self.ealloc_exp(right)
                return BinOp(new_left, operator, new_right)

            case BoolOp(operator, [left, right]):
                new_left = self.ealloc_exp(left)
                new_right = self.ealloc_exp(right)
                return BoolOp(operator, [new_left, new_right])

            case Call(Name(func), []):
                return Call(Name(func), [])

            case Call(Name(func), [attr]):
                new_attr = self.ealloc_exp(attr)
                return Call(Name(func), [new_attr])

            case Compare(left, [cmp], [right]):
                new_left = self.ealloc_exp(left)
                new_right = self.ealloc_exp(right)
                return Compare(new_left, [cmp], [new_right])

            case Constant(value):
                return e

            case IfExp(test, body, orelse):
                new_test = self.ealloc_exp(test)
                new_body = self.ealloc_exp(body)
                new_orelse = self.ealloc_exp(orelse)
                return IfExp(new_test, new_body, new_orelse)

            case Name(var):
                return e

            case Subscript(exp, integer, load):
                new_exp = self.ealloc_exp(exp)
                return Subscript(new_exp, integer, load)

            case Tuple(exps, load):
                type_tup = e.has_type
                new_exps = [self.ealloc_exp(exp) for exp in exps]
                return self.ealloc_tuple(new_exps, type_tup)

            case UnaryOp(operator, exp):
                new_exp = self.ealloc_exp(exp)
                return UnaryOp(operator, new_exp)

            case _:
                raise Exception('error ealloc_exp, unhandled: ' + repr(e))


    def ealloc_stmt(self, s: stmt): #-> List[stmt]:
        match s:
            case Assign([var], exp):
                #new_var = self.ealloc_exp(var)  # bue: maybe not needed since atomic?
                new_exp = self.ealloc_exp(exp)
                return Assign([var], new_exp)

            case Expr(exp):
                new_exp = self.ealloc_exp(exp)
                return Expr(new_exp)

            case If(test, body, orelse):
                new_test = self.ealloc_exp(test)
                new_body = [self.ealloc_stmt(stm) for stm in body]
                new_orelse = [self.ealloc_stmt(stm) for stm in orelse]
                return If(new_test, new_body, new_orelse)

            case While(exp, stmts, []):
                new_exp = self.ealloc_exp(exp)
                new_stmts = [self.ealloc_stmt(stm) for stm in stmts]
                return While(new_exp, new_stmts, [])

            case _:
                raise Exception('error ealloc_stmt, unhandled: ' + repr(s))


    def expose_allocation(self, p: Module) -> Module:
        match p:
            case Module(body):
                l_stm = []
                for stm in body:
                    abc = self.ealloc_stmt(stm)
                    l_stm.append(abc)
                return Module(l_stm)

            case _:
                raise Exception('error expose_allocation, unhandled: ' + repr(p))


    ############################################################################
    # Remove Complex Operands Lalloc -> Lmonalloc
    ############################################################################


    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr,Temporaries]:
        match e:
            case Allocate(i_int, t_type):
                return e, []

            case Begin(stmts, exp):
                new_stmts = [self.rco_stmt(stm) for stm in stmts]
                new_exp, tmp_new = self.rco_exp(exp, False)
                return Begin(sum(new_stmts, []), new_exp), tmp_new

            case BinOp(left, op, right):
                (l, bs1) = self.rco_exp(left, True)
                (r, bs2) = self.rco_exp(right, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    b = BinOp(l, op, r)
                    return tmp, bs1 + bs2 + [(tmp, b)]
                else:
                    return BinOp(l, op, r), bs1 + bs2

            case Call(func, args):
                (new_func, bs1) = self.rco_exp(func, True)
                (new_args, bss2) = unzip([self.rco_exp(arg, True) for arg in args])
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return (tmp, bs1 + sum(bss2, []) + [(tmp, Call(new_func, new_args, []))])
                else:
                    return Call(new_func, new_args, []), bs1 + sum(bss2, [])

            case Compare(left, [op], [right]):
                (l, bs1) = self.rco_exp(left, True)
                (r, bs2) = self.rco_exp(right, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, bs1 + bs2 + [(tmp, Compare(l, [op], [r]))]
                else:
                    return Compare(l, [op], [r]), bs1 + bs2

            case Constant(value):
                if need_atomic and self.big_constant(e):
                    tmp = Name(generate_name('tmp'))
                    return tmp, [(tmp, Constant(value))]
                else:
                    return e, []

            case GlobalValue(variable):
                return e, []

            case IfExp(test, body, orelse):
                (new_test, bs1) = self.rco_exp(test, False)
                (new_body, bs2) = self.rco_exp(body, False)
                (new_orelse, bs3) = self.rco_exp(orelse, False)
                new_body = make_begin(bs2, new_body)
                new_orelse = make_begin(bs3, new_orelse)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return (tmp, bs1 + [(tmp, IfExp(new_test, new_body, new_orelse))])
                else:
                    return IfExp(new_test, new_body, new_orelse), bs1

            case Name(variable):
                return e, []

            case Subscript(atm1, atm2, Load()):
                (new_atm1, tmp1) = self.rco_exp(atm1, True)
                (new_atm2, tmp2) = self.rco_exp(atm2, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    scr = Subscript(new_atm1, new_atm2, Load())
                    return tmp, tmp1 + tmp2 + [(tmp, scr)]
                else:
                    return Subscript(new_atm1, new_atm2, Load()), tmp1 + tmp2

            case Subscript(atm1, atm2, Store()):
                (new_atm1, tmp1) = self.rco_exp(atm1, True)
                (new_atm2, tmp2) = self.rco_exp(atm2, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    scr = Subscript(new_atm1, new_atm2, Store())
                    return tmp, tmp1 + tmp2 + [(tmp, scr)]
                else:
                    return Subscript(new_atm1, new_atm2, Store()), tmp1 + tmp2

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

            case _:
                raise Exception('error in rco_exp, unhandled: ' + repr(e))


    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Assign([Subscript(atm1, atm2, store), rhs]):
                new_atm1, tmp_atm1 = self.rco_exp(atm1, True)
                new_atm2, tmp_atm2 = self.rco_exp(atm2, True)
                new_rhs, tmp_rhs = self.rco_exp(rhs, True)
                return [Assign([Subscript(new_atm1, new_atm2, store)], new_rhs)]

            case Assign(targets, value):
                new_value, bs = self.rco_exp(value, False)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] + [Assign(targets, new_value)]

            case Collect(integer):
                return [Collect(integer)]

            case Expr(value):
                new_value, bs = self.rco_exp(value, False)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] + [Expr(new_value)]

            case If(test, body, orelse):
                new_test, bs = self.rco_exp(test, False)
                new_body = [self.rco_stmt(stm) for stm in body]
                new_orelse = [self.rco_stmt(stm) for stm in orelse]
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] + [If(new_test, sum(new_body, []), sum(new_orelse, []))]

            case While(test, body, []):
                new_test, l_tmp = self.rco_exp(test, False)
                new_test = make_begin(l_tmp, new_test)
                new_body = [self.rco_stmt(stm) for stm in body]
                return [While(new_test, sum(new_body, []), [])]

            case _:
                raise Exception('error in rco_stmt, unhandled: ' + repr(s))


    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(body):
                sss = [self.rco_stmt(stm) for stm in body]
                return Module(sum(sss, []))

            case _:
                raise Exception('error remove_complex_operators, unhandled: ' + repr(p))


    ############################################################################
    # Explicate Control
    ############################################################################

    def create_block(self, stmts: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match stmts:
            case [Goto(label)]:
                return stmts

            case _:
                label = generate_name('block')
                basic_blocks[label] = stmts
                return [Goto(label)]


    def create_loop(self, stmts: List[stmt], cont: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match stmts:
            case [While(test, body, [])]:
                label = generate_name('loop')
                new_cont = self.create_block(cont, basic_blocks)
                new_body = [Goto(label)]
                for i in reversed(body):
                    new_body = self.explicate_stmt(i, new_body, basic_blocks)
                stmts = self.explicate_pred(test, new_body, new_cont, basic_blocks)
                basic_blocks[label] = stmts
                return [Goto(label)]

            case _:
                raise Exception('error create_loop, unhandled: ' + repr(stmts))


    def explicate_effect(self, e: expr, cont: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Begin(body, result):
                ss = self.explicate_effect(result, cont, basic_blocks)
                for s in reversed(body):
                    ss = self.explicate_stmt(s, ss, basic_blocks)
                return ss

            case Call(func, args):
                return [Expr(e)] + cont

            case IfExp(test, body, orelse):
                goto = self.create_block(cont, basic_blocks)
                new_body = self.explicate_effect(body, goto, basic_blocks)
                new_orelse = self.explicate_effect(orelse, goto, basic_blocks)
                return self.explicate_pred(test, new_body, new_orelse, basic_blocks)

            case _:  # no effect, remove this expression
                return cont


    def explicate_assign(self, e: expr, x: Variable, cont: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Begin(body, result):
              ss = self.explicate_assign(result, x, cont, basic_blocks)
              for s in reversed(body):
                  ss = self.explicate_stmt(s, ss, basic_blocks)
              return ss

            case IfExp(test, body, orelse):
                goto = self.create_block(cont, basic_blocks)
                new_body = self.explicate_assign(body, x, goto, basic_blocks)
                new_orelse = self.explicate_assign(orelse, x, goto, basic_blocks)
                return self.explicate_pred(test, new_body, new_orelse, basic_blocks)

            case _:
                return [Assign([x], e)] + cont


    def generic_explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        return [If(Compare(cnd, [Eq()], [Constant(False)]), self.create_block(els, basic_blocks), self.create_block(thn, basic_blocks))]


    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Begin(body, result):
                ss = self.explicate_pred(result, thn, els, basic_blocks)
                for s in reversed(body):
                    ss = self.explicate_stmt(s, ss, basic_blocks)
                return ss

            case Compare(left, [op], [right]):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                return [If(cnd, goto_thn, goto_els)]

            case Constant(True):
                return thn

            case Constant(False):
                return els

            case IfExp(test, body, orelse):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                new_body = self.explicate_pred(body, goto_thn, goto_els, basic_blocks)
                new_els = self.explicate_pred(orelse, goto_thn, goto_els, basic_blocks)
                return self.explicate_pred(test, new_body, new_els, basic_blocks)

            case Name(x):
                return self.generic_explicate_pred(cnd, thn, els, basic_blocks)

            case Subscript(atm1, atm2, Load()):
                tmp = Name(generate_name('tmp'))
                new_assign = [Assign([Name(var)], Subscript(atm1, atm2, Load()))]
                return new_assign + self.generic_explicate_pred(tmp, thn, els, basic_blocks)

            case UnaryOp(Not(), operand):
                return self.explicate_pred(operand, els, thn, basic_blocks)

            case _:
                raise Exception('explicate_pred: unexpected ' + repr(cnd))


    def explicate_stmt(self, s: stmt, cont: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)

            case Collect(integer):
                return [Collect(integer)] + cont

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
                return self.explicate_pred(test, new_body, new_els, basic_blocks)

            case While(test, body, []):
                label = generate_name('loop')
                new_body = [Goto(label)]
                for i in reversed(body):
                    new_body = self.explicate_stmt(i, new_body, basic_blocks)
                stmts = self.explicate_pred(test, new_body, cont, basic_blocks)
                basic_blocks[label] = stmts
                return [Goto(label)]

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

    def select_op(self, op: operator) -> str:
        match op:
            case Sub():
                return 'subq'
            case And():
                return 'andq'
            case Eq():
                return 'e'
            case Is():
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
            case Add():
                return 'addq'
            case Sub():
                return 'subq'
            case USub():
                return 'negq'
            case _:
                raise Exception('select_op unhandled: ' + repr(op))

    def select_exp(self, a: expr) -> arg:
        match a:
            case BinOp(l, Add(), r):
                return BinOp(self.select_exp(l), Add(), self.select_exp(r))

            case BinOp(l, Sub(), r):
                return BinOp(self.select_exp(l), Sub(), self.select_exp(r))

            case Constant(True):
                return Immediate(1)

            case Constant(False):
                return Immediate(0)

            case Constant(value):
                return Immediate(value)

            case GlobalValue(value):
                return Global(value)

            case Name(value):
                return Variable(value)

            case Reg(value):  # cause how we handle Return
                return Reg(value)

            case Subscript(atm1, atm2, Store()):
                return self.select_exp(atm1)

            case _:
                raise Exception('select_exp unhandled: ' + repr(a))


    def select_stmt(self, s: stmt) -> List[instr]:
        ptr_tag = 0
        match s:

#ptr_tag = 0
#i = 7
#for t in ts:
#    ptr_tag |= bool2int(drlf.is_root_type(t)) << i
#    i += 1


# case Assign([lhs], Allocate(length, TupleType(ts))):
#pointer_mask | length | forwarding
#length_tag = length << 1  # bit shift
#[0000000]

            case Assign([lhs], Allocate(length, TupleType(ty))):
                print("BUX!!!:", Allocate(length, TupleType(ty))._fields)
                new_lhs = self.select_exp(lhs)
                new_len = 8 * (length + 1)
                #print('repr: ',[Instr('movq',[Global('free_ptr'),Reg('r11')]),Instr('addq',[new_len,Global('free_ptr')]),Instr('movq',[Immediate(pointer_tag),Reg('rsi')])])
                return [
                    Instr('movq', [Global('free_ptr'), Reg('r11')]),
                    Instr('addq', [Immediate(new_len), Global('free_ptr')]),
                    Instr('movq', [Immediate(ptr_tag), Reg('rsi')])
                ]

            case Assign([lhs], BinOp(left, Add(), right)) if left == lhs:
                new_lhs = self.select_exp(lhs)
                r = self.select_exp(right)
                return [Instr('addq', [r, new_lhs])]

            case Assign([lhs], BinOp(left, Add(), right)) if right == lhs:
                new_lhs = self.select_exp(lhs)
                l = self.select_exp(left)
                return [Instr('addq', [l, new_lhs])]

            case Assign([lhs], BinOp(left, Sub(), right)) if left == lhs:
                new_lhs = self.select_exp(lhs)
                r = self.select_exp(right)
                return [Instr('subq', [r, new_lhs])]

            case Assign([lhs], BinOp(left, Sub(), right)) if right == lhs:
                new_lhs = self.select_exp(lhs)
                l = self.select_exp(left)
                # why not use subq?
                return [
                    Instr('negq', [new_lhs]),
                    Instr('addq', [l, new_lhs])
                ]

            case Assign([lhs], BinOp(left, op, right)):
                new_lhs = self.select_exp(lhs)
                l = self.select_exp(left)
                r = self.select_exp(right)
                return [
                    Instr('movq', [l, new_lhs]),
                    Instr(self.select_op(op), [r, new_lhs])
                ]

            case Assign([lhs], Call(Name('input_int'), [])):
                new_lhs = self.select_exp(lhs)
                return [
                    Callq('read_int', 0),
                    Instr('movq', [Reg('rax'), new_lhs])
                ]

#case Assign([lhs], Call(Name('len'), [tup]

            case Assign([lhs], Call(Name('print'), [operand])):
                return [
                    Instr('movq', [self.select_exp(operand), Reg('rdi')]),
                    Callq('print_int', 1)
                ]

            case Assign([lhs], Compare(left, [op], [right])):
                new_lhs = self.select_exp(lhs)
                l = self.select_exp(left)
                r = self.select_exp(right)
                # in cmpq, the left and right get swapped. -Jeremy
                if isinstance(r, Immediate):
                    comparison = [
                        Instr('movq', [l, Reg('rax')]),
                        Instr('cmpq', [r, Reg('rax')])
                    ]
                else:
                    comparison = [Instr('cmpq', [r, l])]
                return comparison + [
                    Instr('set' + self.select_op(op), [ByteReg('al')]),
                    Instr('movzbq', [ByteReg('al'), new_lhs])
                ]

            case Assign([lhs], Constant(value)):
                new_lhs = self.select_exp(lhs)
                rhs = self.select_exp(Constant(value))
                return [Instr('movq', [rhs, new_lhs])]

            case Assign([lhs], Name(value)):
                print("BUE!!!:", Name(value)._fields)
                print("BUE!!!:", Name(value).id)
                new_lhs = self.select_exp(lhs)
                if Name(value) != lhs:
                    return [Instr('movq', [Variable(value), new_lhs])]
                else:
                    return []

            case Assign([lhs], Subscript(atm1, atm2, Load())):
                tup_n = 8 * (int(atm2.value + 1))
                new_lhs = self.select_exp(lhs)
                new_atm1 = self.select_exp(atm1)
                #new_atm2 = self.select_exp(atm2)
                return [
                    Instr('movq', [new_atm1, Reg('r11')]),
                    Instr('movq', [Deref('r11', tup_n), new_lhs])
                ]

            case Assign([Subscript(atm1, atm2, Store())], atm3):
                tup_n = 8 * (int(atm2.value + 1))
                new_atm1 = self.select_exp(atm1)
                #new_atm2 = self.select_exp(atm2)
                new_atm3 = self.select_exp(atm3)
                return [
                    Instr('movq', [new_atm1, Reg('r11')]),
                    Instr('movq', [new_atm3, Deref('r11', tup_n)])
                ]

            case Assign([lhs], UnaryOp(Not(), operand)):
                new_lhs = self.select_exp(lhs)
                new_operand = self.select_exp(operand)
                return ([Instr('movq', [new_operand, new_lhs])]
                        if new_lhs != new_operand else []) \
                    + [Instr('xorq', [Immediate(1), new_lhs])]

                # bue 20241111: i think the return above for the reference compiler is not functinal!
                #l_inst = [Instr('xorq', [Immediate(1), new_lhs]
                #if new_lhs != new_operand:
                #    l_inst.insert(0, Instr('movq', [new_operand, new_lhs]) )
                #return l_inst

            case Assign([lhs], UnaryOp(USub(), Constant(i))):
                new_lhs = self.select_exp(lhs)
                # not just an optimization; needed to handle min-int
                return [Instr('movq', [Immediate(neg64(i)), new_lhs])]

            case Assign([lhs], UnaryOp(op, operand)):
                new_lhs = self.select_exp(lhs)
                rand = self.select_exp(operand)
                return [
                    Instr('movq', [rand, new_lhs]),
                    Instr(self.select_op(op), [new_lhs])
                ]

            case Collect(integer):
                return [
                    Instr('movq', [Reg('r15'), Reg('rdi')]),
                    Instr('movq', [Immediate(integer), Reg('rsi')]), Callq('collect', integer)
                ]

            case Expr(Call(Name('input_int'), [])):
                return [Callq('read_int', 0)]

            case Expr(Call(Name('print'), [operand])):
                return [
                    Instr('movq', [self.select_exp(operand), Reg('rdi')]),
                    Callq('print_int', 1)
                ]

            case Expr(value):
                return []

            case Goto(label):  # tail
                return [Jump(label)]

            case If(Compare(left, [op], [right]), [Goto(thn)], [Goto(els)]):  # tail
                l = self.select_exp(left)
                r = self.select_exp(right)
                return [
                    Instr('cmpq', [r, l]),
                    JumpIf(self.select_op(op), thn),
                    Jump(els)
                ]

            case Return(value):  # tail
                ins = self.select_stmt(Assign([Reg('rax')], value))
                return ins + [Jump('conclusion')]

            case _:
                raise Exception('error in select_stmt, unknown: ' + repr(s))


    #def select_instructions(self, p: Module) -> X86Program:
    #    match p:
    #        case Module(body):
    #            sss = [self.select_stmt(s) for s in body]
    #            return X86Program(sum(sss, []))

    def select_instructions(self, p: CProgram) -> X86Program:
        match p:
            case CProgram(body):
                blocks = {}
                for (l, ss) in body.items():
                    blocks[l] = sum([self.select_stmt(s) for s in ss], [])
                x = X86Program(blocks)
                x.var_types = p.var_types
                return x


    ###########################################################################
    # Uncover Live
    ###########################################################################
    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case ByteReg(id):
                return {Reg(byte_to_full_reg[id])}
            case Variable(id):
                return {a}
            case Reg(id):
                return {a}
            case Deref(reg, offset):  # don't need this case
                return {Reg(reg)}  # problem for write?
            case Immediate(value):
                return set()
            case Global(label):
                print("HELLO GLOBAL")
                return {}
            
            case _:
                raise Exception('error in vars_arg, unhandled: ' + repr(a))

    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Jump(label):
                return set()
            case JumpIf(cc, label):
                return set()
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
            case Jump(label):
                return set()
            case JumpIf(cc, label):
                return set()
            case Instr('cmpq', args):
                return {Reg('__flag')}
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

    #def uncover_live_instr(self,
    #        i: instr,
    #        e_live_before_succ: Set[location],
    #        de_live_before: Dict[instr, Set[location]],
    #        de_live_after: Dict[instr, Set[location]]
    #    ):
    #    de_live_after[i] = e_live_before_succ
    #    de_live_before[i] = de_live_after[i].difference(self.write_vars(i)).union(self.read_vars(i))

    @staticmethod
    def adjacent_instr(s: instr) -> List[str]:
        if isinstance(s, Jump) or isinstance(s, JumpIf):
            return [s.label]
        else:
            return []

    def blocks_to_graph(self, blocks: Dict[str, List[instr]]) -> DirectedAdjList:
        graph = DirectedAdjList()
        for u in blocks.keys():
            graph.add_vertex(u)
        for (u, ss) in blocks.items():
            for s in ss:
                for v in self.adjacent_instr(s):
                    graph.add_edge(u, v)
        return graph

    #def trace_live_blocks(self,
    #        blocks,
    #        live_before: Dict[instr, Set[location]],
    #        live_after: Dict[instr, Set[location]]
    #    ):
    #    for (l, ss) in blocks.items():
    #        trace(l + ':\n')
    #        i = 0
    #        for s in ss:
    #            if i == 0:
    #                trace('\t\t{' + ', '.join([str(l) for l in live_before[s]]) + '}')
    #            trace(str(s))
    #            trace('\t\t{' + ', '.join([str(l) for l in live_after[s]]) + '}')
    #            i = i + 1

    #def trace_live(self, p: X86Program, live_before: Dict[instr, Set[location]],
    #               live_after: Dict[instr, Set[location]]):
    #    match p:
    #      case X86Program(body):
    #        i = 0
    #        for s in body:
    #            if i == 0:
    #                trace('\t' + str(live_before[s]))
    #            trace(str(s))
    #            trace('\t' + str(live_after[s]))
    #            i = i + 1
    #        trace("")

    #def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
    #    match p:
    #        case X86Program(body):
    #            live_before = {}
    #            live_after = {}
    #            live_before_succ = set([])
    #            for i in reversed(body):
    #                self.uncover_live_instr(i, live_before_succ, live_before,
    #                                        live_after)
    #                live_before_succ = live_before[i]
    #
    #            trace("uncover live:")
    #            self.trace_live(p, live_before, live_after)
    #            return live_after

    #def trace_live(self,
    #        p: X86Program,
    #        live_before: Dict[instr, Set[location]],
    #        live_after: Dict[instr, Set[location]]
    #    ):
    #    match p:
    #        case X86Program(body):
    #            self.trace_live_blocks(body, live_before, live_after)


    def transfer(self, s_node, e_live_after_block, de_live_before, body):
        # bue 20241029: maybe rewrite as transfer function generator
        '''
        input:
            s_node: block lable.
            e_live_after: live after set for that block.

        output:
            e_live_before: live before set for that block.
                as a side effect, update live before and live after set
                for each instruction.

        description:
            apply liveness analysis to ONE block.
        '''
        #print('\ne_live_before block:', s_node)
        e_live_before_block = None
        if s_node == 'conclusion':
            e_live_before_block = {Reg('rax'), Reg('rsp')}  # bue
        else:
            e_live_after = e_live_after_block
            for i in reversed(body[s_node]):  # bue: process block bottom up
                if not(i in de_live_before.keys()):
                    de_live_before[i] = set()
                de_live_before[i] = de_live_before[i].union(e_live_after.difference(self.write_vars(i)).union(self.read_vars(i)))
                #print('e_live_before:', s_node, i, de_live_before[i])
                e_live_after = de_live_before[i]
            e_live_before_block = de_live_before[i]
        return e_live_before_block


    #join = lambda n,m : n.join(m)
    def analyze_dataflow(self, g, transfer, body, e_bottom=set(), join=set.union):
        '''
        input:
            g: transpose of the cfg
            transfer: function to apply liveness analysis to a basic block.
            e_bottom: set of location.
            join: set of location.

        output:
            de_live_before: dictionary of live before location sets,
            one per instruction, ready to be used for assigne homes.

        description:
            note: this function is running on forward analysis input.
            so, if you wanna do a backwards analysis,
            transpose your graph before input.
        '''
        #print('BUE begin analyze data fow!')
        trans_g = transpose(g)
        #print('BUE g:', g.show())
        #print('BUE trans_g:', trans_g.show())
        de_live_before = {}
        de_live_before_block = dict((v, e_bottom) for v in g.vertices())
        de_live_before_block['conclusion'] = {Reg('rax'), Reg('rsp')}  # bue
        ls_work = deque(g.vertices())
        #print('BUE ls_work!', ls_work)
        while ls_work:
            s_node = ls_work.pop()
            le_live_after_block = [de_live_before_block[s_vertex] for s_vertex in trans_g.adjacent(s_node)]  # bue: adjacent are downstream nodes => live after set
            e_live_after_block = reduce(join, le_live_after_block, e_bottom)
            e_live_before_block = transfer(s_node, e_live_after_block, de_live_before=de_live_before, body=body)
            #print('BUE e_live_before_block!', e_live_before_block)
            if e_live_before_block != de_live_before_block[s_node]:
                de_live_before_block[s_node] = e_live_before_block
                ls_work.extend(g.adjacent(s_node))
        #print('BUE end analyze data fow!')
        return de_live_before


    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(body):
                de_live_before = {}
                de_live_after = {}

                cfg = self.blocks_to_graph(body)
                cfg = transpose(cfg)

                #cfg_trans = transpose(cfg)
                #live_before_block = {'conclusion': {Reg('rax'), Reg('rsp')}}

                #for l in topological_sort(cfg_trans):
                #    if l != 'conclusion':
                #        adj_live = [live_before_block[v] for v in cfg.adjacent(l)]
                #        live_before_succ = set().union(*adj_live)
                #        for i in reversed(body[l]):
                #            self.uncover_live_instr(i, live_before_succ, live_before, live_after)
                #            live_before_succ = live_before[i]
                #        live_before_block[l] = live_before_succ

                de_live_before = self.analyze_dataflow(g=cfg, transfer=self.transfer, body=body)

                #trace("uncover live:")
                #self.trace_live(p, live_before=de_live_before, live_after=de_live_after)
                #print('BUE de_live_before:', de_live_before)
                return de_live_before


    ###########################################################################
    # Build Interference
    ###########################################################################

    #def build_interference(self, p: X86Program,
    #                       live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
    #    match p:
    #        case X86Program(body):
    #            G = UndirectedAdjList()
    #            for i in body:
    #                self.interfere_instr(i, G, live_after)
    #            return G


    def build_interference_blocks(self,
            blocks,
            live_after: Dict[instr, Set[location]],
            var_types: Dict
        ) -> UndirectedAdjList:
        graph = UndirectedAdjList()
        for (l, ss) in blocks.items():
            for i in ss:
                self.interfere_instr(i, graph, live_after, var_types)
        return graph


    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(blocks):
                return self.build_interference_blocks(blocks, live_after, p.var_types)


    def interfere_instr(self, i: instr, graph,
                        live_after: Dict[instr, Set[location]],
                        var_types: Dict):  # graph: UndirectedAdjList
        match i:
            case Instr('movzbq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)
                        self.type_edge(d, var_types, graph)

            case Instr('movq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)
                        self.type_edge(d, var_types, graph)

            case _:
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d:
                            graph.add_edge(d, v)
                        self.type_edge(d, var_types, graph)

    def type_edge(self, var, var_types, graph):
        try:
            if type(var_types[var]) == TupleType:
                for node in callee_saved:
                    graph.add_edge(var, node)
        except KeyError:
            pass


    ############################################################################
    # Assign Homes
    ############################################################################

    def collect_locals_instr(self, i: instr) -> Set[location]:
        match i:
            case JumpIf(cc, label):
                return set()
            case Jump(label):
                return set()
            case Instr(inst, args):
                lss = [self.collect_locals_arg(a) for a in args]
                return set().union(*lss)
            case Callq(func, num_args):
                return set()
            case _:
                raise Exception('error in collect_locals_instr, unknown: ' + repr(i))

    def collect_locals_arg(self, a: arg) -> Set[location]:
        match a:
            case ByteReg(id):
                return set()
            case Reg(id):
                return set()
            case Variable(id):
                return {Variable(id)}
            case Immediate(value):
                return set()
            case Deref(reg, offset):
                return set()
            case Global(name):
                return set()
            case _:
                raise Exception('error in collect_locals_arg, unknown: ' + repr(a))

    def collect_locals_instrs(self, ss: List[stmt]) -> Set[location]:
        return set().union(*[self.collect_locals_instr(s) for s in ss])

    @staticmethod
    def gen_stack_access(i: int) -> arg:
        return Deref('rbp', -(8 + 8 * i))

    def assign_homes_arg(self, a: arg, home: Dict[location, arg]) -> arg:
        match a:
            case ByteReg(id):
                return a
            case Reg(id):
                return a
            case Variable(id):
                return home.get(a, a)
            case Immediate(value):
                return a
            case Deref(reg, offset):
                return Deref(reg, offset)
            case Global(name):
                return a
            case _:
                raise Exception('error in assign_homes_arg, unknown: ' + repr(a))

    def assign_homes_instr(self, i: instr, home: Dict[location, arg]) -> instr:
        match i:
            case JumpIf(cc, label):
                return i
            case Jump(label):
                return i
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

    #def assign_homes(self, p: X86Program) -> X86Program:
    #    match p:
    #        case X86Program(body):
    #            variables = self.collect_locals_instrs(body)
    #            home = {}
    #            for i, x in enumerate(variables):
    #                home[x] = self.gen_stack_access(i)
    #            body = self.assign_homes_instrs(body, home)
    #            p = X86Program(body)
    #            p.stack_space = align(8 * len(variables), 16)
    #            return p

    def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
        print("Hallo3:", pseudo_x86.var_types)
        print([type(ty) == TupleType for var, ty in pseudo_x86.var_types.items()])
        live_after = self.uncover_live(pseudo_x86)
        graph = self.build_interference(pseudo_x86, live_after)
        #trace(graph.show().source)
        #trace("")
        return self.allocate_registers(pseudo_x86, graph)


    ###########################################################################
    # Allocate Registers
    ###########################################################################

# valid color
# will be reduced
# separate color for regular stack and root stack
# by even or odd
#odd_registers
#: List[str] = ['r9', 'r11', 'r13']  # root
#even_registers 
#: List[str] = ['r8', 'r10', 'r12', 'r14']  # regular
# the one has an offset
# vector
# integer
# care full no integeer n the roor stack.

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
        print('colors ', color)
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

    #def allocate_registers(self, p: X86Program,
    #                       graph: UndirectedAdjList) -> X86Program:
    #    match p:
    #        case X86Program(body):
    #            variables = self.collect_locals_instrs(body)
    #            (color, spills) = self.color_graph(graph, variables)
    #            trace("color")
    #            trace(color)
    #            trace("")
    #            used_callee = self.used_callee_reg(variables, color)
    #            num_callee = len(used_callee)
    #            home = {}
    #            for x in variables:
    #                home[x] = self.identify_home(color[x], 8 + 8 * num_callee)
    #            trace("home")
    #            trace(home)
    #            trace("")
    #            new_body = [self.assign_homes_instr(s, home) for s in body]
    #            new_p = X86Program(new_body)
    #            new_p.stack_space = align(8 * (num_callee + len(spills)), 16) \
    #                - 8 * num_callee
    #            new_p.used_callee = used_callee
    #            return new_p

    def alloc_reg_blocks(self, blocks, graph: UndirectedAdjList) -> X86Program:
        variables = set().union(*[self.collect_locals_instrs(ss) for (l, ss) in blocks.items()])
        (color, spills) = self.color_graph(graph, variables)

        used_callee = self.used_callee_reg(variables, color)
        num_callee = len(used_callee)
        home = {x: self.identify_home(color[x], 8 + 8 * num_callee) for x in variables}
        new_blocks = {l: self.assign_homes_instrs(ss, home) for (l, ss) in blocks.items()}
        return (new_blocks, used_callee, num_callee, spills)

# split for root spill and stack spill
# do thy need to go for register or root register or stack, and where on the stack.
#

    def allocate_registers(self, p: X86Program, graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86Program(blocks):
                (new_blocks, used_callee, num_callee, spills) = self.alloc_reg_blocks(blocks, graph)
                new_p = X86Program(new_blocks)
                new_p.stack_space = align(8 * (num_callee + len(spills)), 16) - 8 * num_callee
                new_p.used_callee = used_callee
                return new_p


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

            case Instr('movq', [s, t]) if s == t:
                return []

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

    #def patch_instructions(self, p: X86Program) -> X86Program:
    #    match p:
    #        case X86Program(body):
    #            new_p = X86Program(self.patch_instrs(body))
    #            new_p.stack_space = p.stack_space
    #            return new_p

    #def patch_instructions(self, p: X86Program) -> X86Program:
    #    match p:
    #        case X86Program(body):
    #            new_p = X86Program(self.patch_instrs(body))
    #            new_p.stack_space = p.stack_space
    #            new_p.used_callee = p.used_callee
    #            return new_p

    def patch_instructions(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                blocks = {l: self.patch_instrs(ss) for (l, ss) in body.items()}
                new_p = X86Program(blocks)
                new_p.stack_space = p.stack_space
                new_p.used_callee = p.used_callee
                return new_p


    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    #def prelude_and_conclusion(self, p: X86Program) -> X86Program:
    #    match p:
    #        case X86Program(body):
    #            prelude = [Instr('pushq', [Reg('rbp')]),
    #                       Instr('movq', [Reg('rsp'), Reg('rbp')]),
    #                       Instr('subq', [Immediate(p.stack_space),Reg('rsp')])]
    #            concl = [Instr('addq', [Immediate(p.stack_space),Reg('rsp')]),
    #                     Instr('popq', [Reg('rbp')]),
    #                     Instr('retq', [])]
    #            return X86Program(prelude + body + concl)

    #def prelude_and_conclusion(self, p: X86Program) -> X86Program:
    #    match p:
    #        case X86Program(body):
    #            save_callee_reg = []
    #            for r in p.used_callee:
    #                save_callee_reg.append(Instr('pushq', [Reg(r)]))
    #            restore_callee_reg = []
    #            for r in reversed(p.used_callee):
    #                restore_callee_reg.append(Instr('popq', [Reg(r)]))
    #            prelude = [Instr('pushq', [Reg('rbp')]), \
    #                    Instr('movq', [Reg('rsp'), Reg('rbp')])] \
    #                   + save_callee_reg \
    #                   + [Instr('subq', [Immediate(p.stack_space),Reg('rsp')])]
    #            concl = [Instr('addq', [Immediate(p.stack_space),Reg('rsp')])] \
    #                    + restore_callee_reg \
    #                    + [Instr('popq', [Reg('rbp')]),
    #                       Instr('retq', [])]
    #            return X86Program(prelude + body + concl)

# check for small heap sizes

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


# libraries
import ast
from ast import *  # Add, BinOP, Call, Constant, expr, Name, Sub, UnaryOP, USub
# https://docs.python.org/3/library/language.html
# https://docs.python.org/3/library/ast.html
# https://greentreesnakes.readthedocs.io/en/latest/
from graph import UndirectedAdjList, DirectedAdjList, transpose, topological_sort
import os
from priority_queue import PriorityQueue
from utils import *  # generate_name, input_int, label_name
from x86_ast import *  # arg, Callq, Deref, Immediate, Instr, Jump, Reg, Retq, Variable, X86Program


# types
from typing import List, Tuple, Set, Dict
Binding = Tuple[Name, expr]
Temporaries = List[Binding]


# const
l_reg_func = [Reg('rdi'), Reg('rsi'), Reg('rdx'), Reg('rcx'), Reg('r8'), Reg('r9')]
e_reg_caller_saved = set(l_reg_func).union({Reg('rax'), Reg('r10'), Reg('r11')})
e_reg_callee_saved = {Reg('rsp'), Reg('rbp'), Reg('rbx'), Reg('r12'), Reg('r13'), Reg('r14'), Reg('r15')}
e_reg = e_reg_caller_saved.union(e_reg_callee_saved)

noncolor_to_reg = {-1 : Reg('rax'), -2 : Reg('rsp'), -3 : Reg('rbp'), -4 : Reg('r11'), -5 : Reg('r15')}
color_to_reg = {0 : Reg('rcx'), 1 : Reg('rdx'), 2 : Reg('rsi'), 3: Reg('rdi'), 4 : Reg('r8'), 5 : Reg('r9'), 6 : Reg('r10'), 7 : Reg('rbx'), 8 : Reg('r12'), 9 : Reg('r13'), 10 : Reg('r14')}
color_to_mem = color_to_reg.copy()
color_to_mem.update(noncolor_to_reg)

reg_to_noncolor = {value : key for key, value in noncolor_to_reg.items()}
reg_to_color = {value : key for key, value in color_to_reg.items()}
mem_to_color = {value : key for key, value in color_to_mem.items()}

#print('l_reg_func:', l_reg_func)
#print('e_reg_caller_saved:', e_reg_caller_saved)
#print('e_reg_callee_saved:', e_reg_callee_saved)
#print('e_reg:', e_reg)
#print()

#print('noncolor_to_reg:', noncolor_to_reg)
#print('color_to_reg:', color_to_reg)
#print('color_to_mem:', color_to_mem)
#print()

#print('reg_to_noncolor:', reg_to_noncolor)
#print('reg_to_color:', reg_to_color)
#print('mem_to_color:', mem_to_color)

# functions

###############################################################################
# partial evaluation
###############################################################################
# chapeter 2 section2.9 and fig 1.5.

def pe_neg(r):
    match r:
        case Constant(n):  # Lint
            return Constant(neg64(n))

        case _:  # Lint
            return UnaryOp(USub(), r)  # Lint

def pe_add(r1, r2):
    match (r1, r2):
        case (Constant(n1),Constant(n2)):  # Lint
            return Constant(add64(n1, n2))

        case _:  # Lint

            return BinOp(r1, Add(), r2)

def pe_sub(r1, r2):
    match (r1, r2):
        case (Constant(n1), Constant(n2)):  # Lint
            return Constant(sub64(n1, n2))

        case _:  # Lint
            return BinOp(r1, Sub(), r2)

def pe_exp(e):
    match e:
        case BinOp(left, Add(), right):  # Lint
            return pe_add(pe_exp(left), pe_exp(right))

        case BinOp(left, Sub(), right):  # Lint
            return pe_sub(pe_exp(left), pe_exp(right))

        case UnaryOp(USub(), v):  # Lint
            return pe_neg(pe_exp(v))

        case Constant(value):  # Lint
            return e

        case Call(Name('input_int'), []):  # Lint
            return e

        case Name(var):  # Lvar
            return Name(var)

        case _:
            raise Exception('Error: pe_exp case not yet implemented.')

def pe_stmt(s):
    match s:
        case Expr(Call(Name('print'), [arg])):  # Lint
            return Expr(Call(Name('print'),) [pe_exp(arg)])

        case Expr(value):  # Lint
            return Expr(pe_exp(value))

        case Assign([Name(var)],exp):  # Lint
            return Assign([pe_exp(Name(var)), pe_exp(exp)])

        case _:
            raise Exception('Error: pe_stmt case not yet implemented.')

def pe_P_int(p):
    match p:
        case Module(body):  # Lint
            new_body = [pe_stmt(s) for s in body]
            return Module(new_body)

        case _:
            raise Exception('Error: pe_P_int case not yet implemented.')


# classes

class Compiler:

    ###########################################################################
    # Shrink: Lif -> Lif
    ###########################################################################
    # chapter 5 section 5.5 shrink the Lif language

    def shrink_exp(self, e: expr) -> expr:
        print('SHRINK_EXP INPUT expr:', e)
        newexp = None

        match e:
            case BoolOp(And(), [exp1, exp2]):  # shrink translation
                newexp = IfExp(self.shrink_exp(exp1), self.shrink_exp(exp2), Constant(False))

            case BoolOp(Or(), [exp1, exp2]):  # shrink translation
                newexp = IfExp(Constant(True), self.shrink_exp(exp1), self.shrink_exp(exp2))

            case Compare(exp1, [cmp], [exp2]):
                newexp = Compare(self.shrink_exp(exp1), [cmp], [self.shrink_exp(exp2)])

            case UnaryOp(operator, exp1):
                newexp = UnaryOp(operator, self.shrink_exp(exp1))

            case BinOp(exp1, operator, exp2):
                newexp = BinOp(self.shrink_exp(exp1), operator, self.shrink_exp(exp2))

            case IfExp(exp1, exp2, exp3):
                newexp = IfExp(self.shrink_exp(exp1), self.shrink_exp(exp2), self.shrink_exp(exp3))

            case _:  # Call(Name('input_int'), []) | Constant(value) | Name(var)
                newexp = e

        print('SHRINK_EXP OUTPUT expr:', newexp)
        return newexp


    def shrink_stmt(self, s: stmt) -> stmt:
        print('SHRINK_STMT INPUT s:', s)
        newstm = None

        match s:
            case Assign([Name(var)], exp1):
                newstm = Assign([Name(var)], self.shrink_exp(exp1))

            case Expr(Call(Name('print'), [exp1])):
                newstm = Expr(Call(Name('print'), [self.shrink_exp(exp1)]))

            case Expr(exp1):
                newstm = Expr(self.shrink_exp(exp1))

            case If(exp1, stm2, stm3):
                newstm = If(self.shrink_exp(exp1), self.shrink_stmt(stm2), self.shrink_stmt(stm3))

            case _:  # [...] block
                newstm = s

        print('SHRINK_STMT OUTPUT smt:', newstm)
        return newstm


    def shrink(self, p: Module) -> Module:
        print('SHRINK INPUT module :', p)
        module = None
        match p:
            case Module(body):  # Lif
                l_stm = []
                for stm in body:
                    l_stm.append(self.shrink_stmt(stm))
                module = Module(l_stm)

            case _:
                raise Exception('Error: Compiler.shrink case not yet implemented.')

        print('SHRINK OUTPUT module :', module)
        return module


    ############################################################################
    # Remove Complex Operands: Lvar -> Lvar mon or Lif -> Lif mon
    ############################################################################
    # trip to x86 chapter 1 and 2 section 2.4 remove compex operands.
    # output: expression and enviroment (expr, [(Name, (expr, [(Name, expr)]))])

    def rco_exp(self, e: expr, need_atomic : bool) -> Tuple[expr, Temporaries]:
        print('RCO_EXP INPUT expr, need_atomic :', e, need_atomic)
        match e:
            case BinOp(left, Add(), right):  # Lint; maybe complex; expr, operator, expr
                newexp1, l_tmp1 = self.rco_exp(left, True)
                newexp2, l_tmp2 = self.rco_exp(right, True)
                add = BinOp(newexp1, Add(), newexp2)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    print('RCO_EXP OUTPUT add complex:', (tmp, l_tmp1 + l_tmp2 + [(tmp, add)]))
                    return (tmp, l_tmp1 + l_tmp2 + [(tmp, add)])
                print('RCO_EXP OUTPUT add atom:', (add, l_tmp1 + l_tmp2))
                return (add, l_tmp1 + l_tmp2)

            case BinOp(left, Sub(), right):  # Lint; maybe complex; expr, operator, expr
                newexp1, l_tmp1 = self.rco_exp(left, True)
                newexp2, l_tmp2 = self.rco_exp(right, True)
                sub = BinOp(newexp1, Sub(), newexp2)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    print('RCO_EXP OUTPUT sub complex:', (tmp, l_tmp1 + l_tmp2 + [(tmp, sub)]))
                    return (tmp, l_tmp1 + l_tmp2 + [(tmp, sub)])
                print('RCO_EXP OUTPUT sub atom:', (sub, l_tmp1 + l_tmp2))
                return (sub, l_tmp1 + l_tmp2)

            #case BoolOp(boolop, [left, right]):
            # bue 20241003: never happens. turned into if stmt in shrink op

            case Call(Name('input_int'), []):  # Lint; always leaf
                inputint = Call(Name('input_int'), [])
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    print('RCO_EXP OUTPUT input_int complex:', (tmp, [(tmp, inputint)]))
                    return (tmp, [(tmp, inputint)])
                print('RCO_EXP OUTPUT input_int atom:', (inputint, []))
                return (inputint, [])

            case Constant(value):  # Lint; Lif; always leaf
                constant = Constant(value)  # bue 20241003: can handel int, bool
                print('RCO_EXP OUTPUT constant atom:', (constant, []))
                return (constant, [])

            case Compare(left, [cmp], [right]):  # Lif; always leaf
                compare = Compare(left, [cmp], [right])  # 20241003: can handel Eq, NotEq, Lt, LtE, Gt, GtE
                print('RCO_EXP OUTPUT compare atom:', compare)
                return (compare, [])

            case IfExp(exptest, expthen, expelse):  # Lif
                # test
                newexptest, l_tmptest = self.rco_exp(exptest, False)
                # then
                newexpthen, l_tmpexpthen = self.rco_exp(expthen, False)
                l_tmpstmtthen = [Assign([Name(var)], exp) for var, exp in l_tmpexpthen]
                #l_tmpstmtthen = [Assign([var], exp) for var, exp in l_tmpexpthen]
                # else
                newexpelse, l_tmpexpelse = self.rco_exp(expelse, False)
                l_tmpstmtelse = [Assign([Name(var)], exp) for var, exp in l_tmpexpelse]
                #l_tmpstmtelse = [Assign([var], exp) for var, exp in l_tmpexpelse]
                # ifexp statement
                # bue 20241009: Begin is part of Lif mon and not part of Lif.
                if (len(l_tmpstmtthen) == 0) and (len(l_tmpstmtelse) == 0):
                    ifexp = IfExp(newexptest, newexpthen, newexpelse)
                elif (len(l_tmpstmtthen) == 0) and (len(l_tmpstmtelse) != 0):
                    ifexp = IfExp(newexptest, newexpthen, Begin(l_tmpstmtelse, newexpelse))
                elif (len(l_tmpstmtthen) != 0) and (len(l_tmpstmtelse) == 0):
                    ifexp = IfExp(newexptest, Begin(l_tmpstmtthen, newexpthen), newexpelse)
                else:
                    ifexp = IfExp(newexptest, Begin(l_tmpstmtthen, newexpthen), Begin(l_tmpstmtelse, newexpelse))
                print('RCO_EXP OUTPUT ifexp:', ifexp, l_tmptest)
                return (ifexp, l_tmptest)

            case Name(var):  # Lvar; always leaf
                name = Name(var)
                print('RCO_EXP OUTPUT var name atom:', (name, []))
                return (name, [])

            # bue 20241003: still have to test
            case UnaryOp(Not(), operand): # Lif
                newexp, l_tmp = self.rco_exp(operand, True)
                noot = UnaryOp(Not(), newexp)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    print('RCO_EXP OUTPUT not complex:', (tmp, l_tmp + [(tmp, noot)]))
                    return (tmp, l_tmp + [(tmp, noot)])
                print('RCO_EXP OUTPUT not atom:', (noot, l_tmp))
                return (noot, l_tmp)

            case UnaryOp(USub(), operand):  # Lint and Lvar; maybe complex; operator, operand
                newexp, l_tmp = self.rco_exp(operand, True)
                neg = UnaryOp(USub(), newexp)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    print('RCO_EXP OUTPUT neg complex:', (tmp, l_tmp + [(tmp, neg)]))
                    return (tmp, l_tmp + [(tmp, neg)])
                print('RCO_EXP OUTPUT neg atom:', (neg, l_tmp))
                return (neg, l_tmp)

            case _:
                raise Exception(f'Error: {e} Compiler.rco_exp case not yet implemented.')


    def rco_stmt(self, s: stmt) -> List[stmt]:
        print('RCO_STMT INPUT stmt:', ast.dump(s))
        l_stmt = None

        match s:
            case Assign([Name(var)], exp):  # Lvar
                newexp, l_tmp =  self.rco_exp(exp, False)  # output: expression and enviroment
                l_stmt =  [Assign([varc], expc) for varc, expc in l_tmp] + [Assign([Name(var)], newexp)]

            case Expr(Call(Name('input_int'), [exp])):  # Lvar
                newexp, l_tmp = self.rco_exp(exp, True)
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmp]

            case Expr(Call(Name('print'), [exp])):  # Lint
                newexp, l_tmp =  self.rco_exp(exp, True)
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmp] + [Expr(Call(Name('print'), [newexp]))]

            # bue 20241009: Expr(exp) have to come after  Expr(Call(Name('abc'), [exp]))
            case Expr(exp):  # Lint
                newexp, l_tmp =  self.rco_exp(exp, False)  # output: expression and enviroment
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmp]

            case If(exptest, stmthen, stmelse):  # Lif
                newexptest, l_tmptest = self.rco_exp(exptest, False)
                #l_stmtmptest = [Assign([Name(generate_name('tmp'))], exp) for exp in l_tmptest]
                l_stmthen = [self.rco_stmt(stm) for stm in stmthen]
                l_stmelse = [self.rco_stmt(stm)  for stm in stmelse]
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmptest] + [If(newexptest, l_stmthen, l_stmelse)]
                #l_stmt = l_stmtmptest + [If(newexptest, l_stmthen, l_stmelse)]
                #l_stmt = l_stmtmptest + [If(newexptest, stmthen, stmelse)]

            case _:
                raise Exception('Error: Compiler.rco_stmt case not yet implemented.')

        print('RCO_STMT OUTPUT l_stmt:', l_stmt)
        return l_stmt


    def remove_complex_operands(self, p: Module) -> Module:
        print('RCO INPUT Module:', ast.dump(p))
        module = None

        match p:
            case Module(body):  # Lint
                l_stmt = []
                for stmt in body:
                    l_stmt.extend(self.rco_stmt(stmt))
                module = Module(l_stmt)

            case _:
                raise Exception('Error: Compiler.remove_complex_operands case not yet implemented.')

        print('RCO OUTPUT module:', ast.dump(module))
        return module


    ###########################################################################
    # explicate control Lif mon -> Cif
    ###########################################################################

    def create_block(stmts : List[stmt], basic_blocks : Dict) -> List:
        # bue: this updates the basic_blocks dict

        match stmts:
            case [Goto(1)]:
                return stmts

            case _:
                label = label_name(generate_name('block'))
                basic_blocks[label] = stmts
                return [Goto(label)]


    def explicate_effect(self, e : expr, cont : List[stmt], basic_blocks : Dict) -> List[stmt]:
        ''' generate code for expressions as statements, result is ignored, only side effects matter '''
        #print('EXPLICATE_EFFECT INPUT:')
        #l_stm = None

        match e:
            case IfExp(test, body, orelse):
                cont_block = self.create_block(cont, basic_blocks)
                body_block = self.create_block(body, basic_blocks)
                orelse_block = self.create_block(orelse, basic_blocks)
                new_test = self.explicate_pred(test, body_block, orelse_block, basic_blocks)
                return new_test

            case Call(func, args):
                return Expr(Call(func, args))

            case Begin(body, result):
                new_block = self.create_block(cont, basic_blocks)
                new_body = self.explicate_effect(body, new_block, basic_blocks)
                return new_body

            case _:
                pass

        #print('EXPLICATE_EFFECT OUTPUT l_stm:', l_stm)
        #return l_stm


    def explicate_assign(self, rhs, lhs, cont : List[stmt], basic_blocks : Dict) -> List[stmt]:
        ''' generate code for a right hand side expressions of an assignment '''
        #print('EXPLICATE_ASSIGN INPUT:')
        #l_stm = None

        match rhs:
            case IfExp(test, body, orelse):
                cont_block = self.create_block(cont, basic_blocks)
                body_assign = self.explicate_assign(body, lhs, cont_block, basic_blocks)
                return [Assign([lhs], body_assign)] + cont_block

            case Begin(body, result):
                cont_block = self.create_block(cont, basic_blocks)
                new_body = self.explicate_assign(body, lhs, cont_block, basic_blocks)
                return [Assign(lhs, new_body)] + cont_block

            case _:
                return [Assign([lhs], rhs)] + cont

        #print('EXPLICATE_ASSIGN OUTPUT l_stm:', l_stm)
        #return l_stm


    def explicate_pred(self, cnd : expr, thn : List[stmt], els : List[stmt], basic_blocks : Dict) -> List[stmt]:
        ''' generate code for if expressions or statement by analyzing the condition expression '''
        #print('EXPLICATE_PRED INPUT:')
        #l_stm = None

        match cnd:
            case Compare(left, [op], [right]):
                goto_thn = create_block(thn, basic_blocks)
                goto_else = create_block(els, basic_blocks)
                return [If(cnd, goto_thn, goto_els)]

            case Constant(True):
                return thn

            case Constant(False):
                return els

            case UnaryOp(Not(), operand):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                o1 = self.explicate_pred(operand, goto_thn, goto_els, basic_blocks)
                return o1

            case IfExp(test, body, orelse):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                b1 = self.explicate_pred(body, goto_thn, goto_els, basic_blocks)
                o1 = self.explicate_pred(orelse, goto_thn, goto_els, basic_blocks)
                new_test = self.explicate_pred(test, b1, o1, basic_blocks)
                return new_test

            case Begin(body, result):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                new_body = self.explicate_pred(body, goto_thn, goto_els, basic_blocks)
                return new_body

            case _:
                l_stm = [If(
                    Compare(cnd, [Eq()], [Constant(False)]),
                    create_block(els, basic_blocks),
                    create_block(thn, basic_blocks)
                )]

        #print('EXPLICATE_PRED OUTPUT l_stm:', l_stm)
        #return l_stm


    def explicate_stmt(self, s : stmt, cont : List, basic_blocks : Dict) -> List[stmt]:
        ''' generate code for statements '''
        #print('EXPLICATE_STMT INPUT:')
        #l_stm = None

        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)

            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)

            case If(test, body, orelse):  # bue 20241006
                return self.explicate_pred(test, body, orelse, basic_blocks)

            case _:
                raise Exception('Error: Compiler.explicate_stmt case not yet implemented.')

        #print('EXPLICATE_STMT OUTPUT l_stm:', l_stm)
        #return l_stm


    def explicate_control(self, p: Module):
        print('EXPLICATE_CTRL INPUT Module:', ast.dump(p))
        cprogram = None

        match p:
            case Module(body):
                new_body = [Return(Constant(0))]
                basic_blocks = {}
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                basic_blocks.update({label_name('start') : new_body})
                cprogram = CProgram(basic_blocks)

            case _:
                raise Exception('Error: Compiler.explicate_control case not yet implemented.')

        print('EXPLICATE_CTRL INPUT CProgram', cprogram)
        return cprogram


    ############################################################################
    # Select Instructions: Lvar mon -> x86var  Cif -> X86var
    ############################################################################
    # trip to x86 chapter 1 and 2 section 2.5 select instructions.

    def select_arg(self, e: expr) -> arg:  # arg terminal
        # work on atoms
        print('SELECT_ARG INPUT expr:', e)
        arg_var = None

        match e:
            case Constant(var):  # Lint atom
                if var:
                    arg_var = Immediate(1)

                elif not var:
                    arg_var = Immediate(0)

                else:
                    arg_var = Immediate(var)

            case Name(var):  # Lvar atom
                arg_var = Variable(var)

            case _:
                raise Exception('Error: Compiler.select_arg case not yet implemented.')

        print('SELECT_ARG OUTPUT arg:', arg_var)
        return arg_var


    def select_stmt(self, s: stmt) -> List[instr]:  # stmt non terminal
        print('SELECT_STMT INPUT stmt:', s)
        l_inst = None

        match s:
            case Assign([Name(var)], Call(Name('input_int'), [])):  # Lint  expr
                arg_var = self.select_arg(Name(var))
                l_inst = [
                    Callq(label_name('read_int'), []),
                    Instr('movq', [Reg('rax'), arg_var]),
                ]

            case Assign([Name(var)], BinOp(left, Add(), right)):  # Lint expr: expr, operator, expr
                arg_var = self.select_arg(Name(var))
                arg_left = self.select_arg(left)
                arg_right = self.select_arg(right)
                if arg_left == arg_var:
                    l_inst = [
                        Instr('addq', [arg_right, arg_var]),
                    ]
                elif arg_right == arg_var:
                    l_inst = [
                        Instr('addq', [arg_left, arg_var]),
                    ]
                else:
                    l_inst = [
                        Instr('movq', [arg_left, arg_var]),
                        Instr('addq', [arg_right, arg_var]),
                    ]

            case Assign([Name(var)], BinOp(left, Sub(), right)):  # Lint expr: expr, operator, expr
                arg_var = self.select_arg(Name(var))
                arg_left = self.select_arg(left)
                arg_right = self.select_arg(right)
                l_inst = [
                    Instr('movq', [arg_left, Reg('rax')]),
                    Instr('subq', [arg_right, Reg('rax')]),
                    Instr('movq', [Reg('rax'), arg_var]),
                ]

            case Assign([Name(var)], exp):  # Lvar stmt
                arg = self.select_arg(exp)
                l_inst = [
                    Instr('movq', [arg, Variable(var)]),
                ]

            case Assign([Name(var)], UnaryOp(USub(), operand)):  # Lint expr : operator, operand
                arg_var = self.select_arg(Name(var))
                arg_operand = self.select_arg(operand)
                l_inst = [
                    Instr('movq', [arg_operand, Reg('rax')]),
                    Instr('negq', [Reg('rax')]),
                    Instr('movq', [Reg('rax'), arg_var]),
                ]

            case Assign([Name(var)], UnaryOp(Not(), operand)):  # Lif expr: operator, operand
                l_instr = None
                arg_var = self.select_arg(Name(var))
                arg_operand = self.select_arg(operand)
                if arg_var == arg_operand :
                    l_inst = [Instr('xorq', [Immediate(1), arg_var])]
                else:
                    l_inst = [
                        Instr('movq', [arg_var, arg_operand]),
                        Instr('xorq', [Immediate(1), arg_var]),
                    ]

            case Expr(Call(Name('print'), [exp])):  # Lint stmt
                arg_exp = self.select_arg(exp)
                l_inst = [
                    Instr('movq', [arg_exp, Reg('rdi')]),
                    Callq(label_name('print_int'), []),
                ]

            # bue 20240915: is terminal. resolved on the select_instructions level.
            #case Expr(exp):  # Lint stmt
            #    arg_exp = self.select_arg(exp)
            #    l_inst = []

            case If(Compare(atm1, [comp], [atm2], [Goto(label1)], [Goto(label2)])):

                atm_one = self.select_arg(atm1)
                atm_two = self.select_arg(atm2)

                if (compare == Eq()):
                    cc = 'e'
                    l_instr = [
                        Instr('cmpq', [atm_one, atm_two]),
                        Instr('JumpIf', cc, label1),
                        Instr('Jump', label2)

                    ]

                elif (compare == GtE()):
                    cc ='ge'
                    l_instr = [
                        Instr('cmpq', [atm_one, atm_two]),
                        Instr('JumpIf', cc, label1),
                        Instr('Jump', label2)
                    ]

                elif (compare == LtE()):
                    cc = 'le'
                    l_instr = [
                        Instr('cmpq', [atm_one, atm_two]),
                        Instr('JumpIf', cc, label1),
                        Instr('Jump', label2)
                    ]

                elif (compare == Lt()):
                    cc = 'l'
                    l_instr = [
                        Instr('cmpq', [atm_one, atm_two]),
                        Instr('JumpIf', cc, label1),
                        Instr('Jump', label2)
                    ]

                elif (compare == Gt()):
                    cc = 'g'
                    l_instr = [
                        Instr('cmpq', [atm_one, atm_two]),
                        Instr('JumpIf', cc, label1),
                        Instr('Jump', label2)
                    ]

                elif (compare == NotEq()):
                    cc = 'ne'
                    l_instr = [
                        Instr('cmpq', [atm_one, atm_two]),
                        Instr('JumpIf', cc, label1),
                        Instr('Jump', label2)
                    ]

                else:
                    raise Exception('Error: Compiler.select_stmt If Compare case not yet implemented.')

            case Return(exp):
                new_exp = self.select_arg(exp)
                l_instr = [
                    Instr('movq',[new_exp,Reg('rax')]),
                    Jump('conclusion')
                ]

            case _:
                raise Exception('Error: Compiler.select_stmt case not yet implemented.')

        print('SELECT_STMT OUTPUT l_inst:', l_inst)
        return l_inst


    def select_instructions(self, p: Module) -> X86Program:
        print('SELECT_INSTRUCTIONS INPUT Module:', ast.dump(p))
        x86program = None

        match p:
            case Module(body):
                d_body = {}
                # BUE 20241008: this might through an error
                for s_label, l_stmt in body.items():
                    l_inst = []
                    for stmt in l_stmt:
                        l_inst.extend(self.select_stmt(stmt))
                    d_body.update({s_label : l_inst})
                x86program = X86Program(d_body)

            case _:
                raise Exception('Error: Compiler.select_instructions case not yet implemented.')

        print('SELECT_INSTRUCTIONS OUTPUT x86program:', x86program)
        return x86program


    ###########################################################################
    # Uncover Live
    ###########################################################################
    # register allocation chapter 4 section 4.2 liveness analysis

    def read_vars(self, i: instr) -> Set[location]:
        print('READ_VARS INPUT:', i)
        e_read = set()

        match i:
            # bue 2024-09-18 nop: popq pushq
            # negq
            case Instr('negq', [Reg(arg)]):  # r
               e_read.add(Reg(arg))

            # movq
            case Instr('movq', [Reg(arg1), arg2]):  # ri, rr, rv
               e_read.add(Reg(arg1))

            case Instr('movq', [Variable(arg1), arg2]):  # vi, vr, vv
               e_read.add(Variable(arg1))

            # addq or subq
            case Instr('addq', [Immediate(arg1), Reg(arg2)]) | Instr('subq', [Immediate(arg1), Reg(arg2)]):  # ir
               e_read.add(Reg(arg2))

            case Instr('addq', [Immediate(arg1), Variable(arg2)]) | Instr('subq', [Immediate(arg1), Variable(arg2)]):  # iv
               e_read.add(Variable(arg2))

            case Instr('addq', [Reg(arg1), Immediate(arg2)]) | Instr('subq', [Reg(arg1), Immediate(arg2)]):  # ri
               e_read.add(Reg(arg1))

            case Instr('addq', [Reg(arg1), Reg(arg2)]) | Instr('subq', [Reg(arg1), Reg(arg2)]):  # rr
               e_read.add(Reg(arg1))
               e_read.add(Reg(arg2))

            case Instr('addq', [Reg(arg1), Variable(arg2)]) | Instr('subq', [Reg(arg1), Variable(arg2)]):  # rv
               e_read.add(Reg(arg1))
               e_read.add(Variable(arg2))

            case Instr('addq', [Variable(arg1), Immediate(arg2)]) | Instr('subq', [Variable(arg1), Immediate(arg2)]):  # vi
               e_read.add(Variable(arg1))

            case Instr('addq', [Variable(arg1), Reg(arg2)]) | Instr('subq', [Variable(arg1), Reg(arg2)]):  # vr
               e_read.add(Variable(arg1))
               e_read.add(Reg(arg2))

            case Instr('addq', [Variable(arg1), Variable(arg2)]) | Instr('subq', [Variable(arg1), Variable(arg2)]):  # vv
               e_read.add(Variable(arg1))
               e_read.add(Variable(arg2))

            # callq
            case Callq('print', i_parameter):  # read form e_reg_caller_saved function register
                 for n in range(i_parameter):
                     e_read.add(Reg(l_reg_func[n]))

            case _:  # callq read_int
                pass

        print('READ_VARS OUTPUT:', e_read)
        return e_read


    def write_vars(self, i: instr) -> Set[location]:
        print('WRITE_VARS INPUT:', i)
        e_write = set()

        match i:
            # bue 2024-09-18 nop: popq pushq
            case Instr('negq', [Reg(arg)]):  # r
                e_write.add(Reg(arg))

            case Instr('negq', [Variable(arg)]):  # v
                e_write.add(Variable(arg))

            # addq, movq, subq
            case Instr(command, [arg1, Reg(arg2)]):  # ir, rr, vr
                e_write.add(Reg(arg2))

            case Instr(command, [arg1, Variable(arg2)]):  # iv, rv, vv
                e_write.add(Variable(arg2))

            # callq
            case Callq(command, i_parameter):  # write into caller saved function registers
                for register in e_reg_caller_saved:
                    e_write.add(register)

            case _:
                pass

        print('WRITE_VARS OUTPUT:', e_write)
        return(e_write)

    def build_cfg(self, p:X86Program)  -> DirectedAdjList: # ctrl flow graph
        print('BUILD_CFG INPUT:', p)
        g = None

        match p:
            case X86Program(body):
                g = DirectedAdjList()

                # walk through the program instructuons
                for src, l_stmt in body.items():
                    for i in l_stmt:
                        match i:
                            case Jump(dst):
                                g.add_edge(src, dst)

                            case JumpIf(cc, dst):
                                g.add_edge(src, dst)

                            case _:
                                pass

        print('BUILD_CFG OUTPUT:', g.show())
        return g


    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        print('UNCOVER_LIVE INPUT:', p)
        d_after = None

        match p:
            case X86Program(body):
                e_location = set()
                e_after = set()
                d_after = {}
                d_live_before_block = {}
                g = build_cfg(p)
                for s_label  in topological_sort(transpose(g)):
                    for i in body[label][::-1]:
                        # bue 20241008: p84 live before block
                        e_read = self.read_vars(i)
                        e_write = self.write_vars(i)
                        e_before = (e_after.difference(e_write)).union(e_read)
                        d_after.update({i: e_after})
                        e_after = e_before
                        e_location = e_location.union(e_read.union(e_write))
                    d_live_before_block.update({s_label : e_before})

            case _:
                raise Exception('Error: Compiler.select_instructions case not yet implemented.')

        print('UNCOVER_LIVE OUTPU dict:', d_after)
        return (d_after, e_location)


    ############################################################################
    # Graph
    ############################################################################
    # register allocation chapter 4 section 4.3 build interference graph
    # register allocation chapter 4 section 4.4 graph coloring via sudoku
    # register allocation chapter 4 section 4.7 move biasing

    def build_interference(self, p: X86Program, live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        print('BUILD_INTERFERENCE INPUT:', p)
        g = None

        match p:
            case X86Program(body):

                g = UndirectedAdjList()

                # add all registers to the graph
                for register in e_reg:
                    g.add_vertex(register)

                # walk through the program instructuons
                for i in body:
                    match i:
                        #case Callq(command, i_parameter):  # print read_int
                        #    for dst in e_reg_caller_saved:  # bue: maybe coved by case _ ?!
                        #        for var in live_after[i]:
                        #            g.add_edge(dst, var)

                        case Instr('movq', [src, dst]) | Instr('movzbq', [src, dst]):
                            for var in live_after[i]:
                                if (var != src) and (var != dst):
                                    g.add_edge(dst, var)

                        case _:
                            e_write = self.write_vars(i)
                            for dst in e_write:
                                for var in live_after[i]:
                                    if (var != dst):
                                        g.add_edge(dst, var)

            case _:
                raise Exception('Error: Compiler.build_interference case not yet implemented.')

        #print('BUILD_INTERFERENCE OUTPUT:', g.show())
        return g


    def build_movegraph(self, p: X86Program) -> UndirectedAdjList:
        print('BUILD_MOVEGRAPH INPUT:', p)
        g = None

        match p:
            case X86Program(body):

                g = UndirectedAdjList()
                for i in body:
                    match i:
                        #case Instr('movq', [Variable(src), Variable(dst)]):
                        case Instr('movq', [Reg(src), Reg(dst)]) | Instr('movq', [Reg(src), Variable(dst)]) | Instr('movq', [Variable(src), Reg(dst)]) | Instr('movq', [Variable(src), Variable(dst)]):
                            g.add_edge(src,dst)

                        case _:
                            pass

            case _:
                raise Exception('Error: Compiler.build_movegraph case not yet implemented.')

        #print('BUILD_MOVEGRAPH OUTPUT:', g.show())
        return g


    # returns the coloring and the set of spilled variables.
    def color_graph(self, graphi: UndirectedAdjList, graphm: UndirectedAdjList, variables: Set[location]) -> Tuple[Dict[location, int], Set[location]]:
        print('COLOR_GRAPH INPUT graphi, graphm, variables:', graphi, graphm, variables)

        # get color integer
        ei_rainbow = set(color_to_reg.keys())

        # get spilled var set
        eo_spilled = set()

        # extract variable objects from graph
        w = set(graphi.vertices())

        # get var color integer mapping
        doi_color = {}
        for o_var in variables:
            doi_color.update({o_var : None})
        for o_mem, i_color in mem_to_color.items():
            doi_color.update({o_mem : i_color})

        # get saturation dictionary
        doe_satur = {}
        for o_var in variables:
            doe_satur.update({o_var : set()})
        for o_mem in mem_to_color.keys():
            doe_satur.update({o_mem : set(mem_to_color.values()).difference({mem_to_color[o_mem]})})

        # build priority queue
        def less(x, y):
            return len(doe_satur[x.key]) < len(doe_satur[y.key])

        def more(x, y):
            if len(doe_satur[x.key]) ==  len(doe_satur[y.key]):
                # update surrounding color
                doe_colorm = {}
                for o_node in {x.key, y.key}:
                    doe_colorm.update({o_node : set()})
                    for o_adj in graphm.adjacent(o_node):
                        try:
                            i_color = doi_color[o_adj]
                            if (i_color != None):
                                doe_colorm[o_node].add(doi_color[o_adj])
                        except KeyError:
                            pass
                print('BUE:', doe_colorm)
                return len(doe_colorm[x.key].difference(doe_satur[x.key])) <= len(doe_colorm[y.key].difference(doe_satur[y.key]))
            else:
                return len(doe_satur[x.key]) < len(doe_satur[y.key])
        pqueue = PriorityQueue(more)
        for o_var, e_satur in doe_satur.items():
            pqueue.push(o_var)

        # traverse the graph
        while pqueue.heap.heap_size != 0:
            # pop most saturated value
            o_var = pqueue.pop()

            # check for non color register
            try:
                i_color = reg_to_noncolor[o_var]

            # choose color
            except KeyError:
                # get lowest color not adjacent
                # if necessary, update rainbow with spilled color
                ei_colorpot = ei_rainbow.difference(doe_satur[o_var])
                if len(ei_colorpot) != 0:
                    i_color = min(ei_colorpot)
                else:
                    i_color = max(ei_rainbow) + 1
                    ei_rainbow.add(i_color)

                # update spilled variable set
                if i_color >= len(color_to_reg):
                    eo_spilled.add(o_var)

                # color variable
                doi_color.update({o_var : i_color})

            # update saturation
            for o_adj in graphi.adjacent(o_var):
                doe_satur[o_adj].add(i_color)

        print('COLOR_GRAPH OUTPUT dict coloring and set spilled var:', doi_color, eo_spilled)
        return (doi_color, eo_spilled)


    ############################################################################
    # Assign Homes: x86var -> x86var
    # Allocate Register
    ############################################################################
    # trip to x86 chapter 1 and 2 section 2.6 assign homes.
    # register allocation chapter 4 section 4.4 graph coloring via sudoku

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        print('ASSIGN_HOMES_ARG INPUT arg home:', a, home)
        argument = None

        match a:
            case Variable(arg):
                argument = home[Variable(arg)]

            case _:
                raise Exception('Error: Compiler.assign_homes_arg case not yet implemented.')

        print('ASSIGN_HOMES_ARG OUTPUT arg:', argument)
        return argument


    def assign_homes_instr(self, i: instr, home: Dict[Variable, arg]) -> instr:
        print('ASSIGN_HOMES_INSTR INPUT instr, home:', i, home)
        instruction = None

        # Immediate, Reg, Variable: 3**2 = 9 [cases]
        # only variables have to be assigned a home
        match i:

            case Instr(command, [Variable(arg)]):  # v
                arg_var1 = self.assign_homes_arg(Variable(arg), home)
                instruction = Instr(command, [arg_var1])

            case Instr(command, [Immediate(arg1), Variable(arg2)]):  # iv
                arg_var2 = self.assign_homes_arg(Variable(arg2), home)
                instruction = Instr(command, [Immediate(arg1), arg_var2])

            case Instr(command, [Reg(arg1), Variable(arg2)]):  # rv
                arg_var2 = self.assign_homes_arg(Variable(arg2), home)
                instruction = Instr(command, [Reg(arg1), arg_var2])

            case Instr(command, [Variable(arg1), Immediate(arg2)]):  # vi
                arg_var1 = self.assign_homes_arg(Variable(arg1), home)
                instruction = Instr(command, [arg_var1, Immediate(arg2)])

            case Instr(command, [Variable(arg1), Reg(arg2)]):  # vr
                arg_var1 = self.assign_homes_arg(Variable(arg1), home)
                instruction = Instr(command, [arg_var1, Reg(arg2)])

            case Instr(command, [Variable(arg1), Variable(arg2)]):  # vv
                arg_var1 = self.assign_homes_arg(Variable(arg1), home)
                arg_var2 = self.assign_homes_arg(Variable(arg2), home)
                instruction = Instr(command, [arg_var1, arg_var2])

            case _:
                instruction = i

        print('ASSIGN_HOMES_INSTR OUTPUT instr:' , instruction)
        return instruction


    def allocate_registers(self, p: X86Program, graphi: UndirectedAdjList, graphm: UndirectedAdjList, variables:  Set[Variable]) -> X86Program:
        print('ALLOCATE_REGISTERS INPUT X86Program, graph, variables:', p, graphi, graphm, variables)
        x86program = None

        match p:
            case X86Program(program):
                # graph coloring
                d_var_to_color, e_var_spilled = self.color_graph(graphi, graphm, variables)

                # variable to memory mapping register and spilled
                d_var_to_memory = {}
                self.stack_space = 0
                for var in set(d_var_to_color.keys()).difference(e_var_spilled):
                    d_var_to_memory.update({var : color_to_mem[d_var_to_color[var]]})
                for var in e_var_spilled:
                    self.stack_space -= 8
                    d_var_to_memory.update({var : Deref('rbp', self.stack_space)})

                # translate x86var to x86
                l_inst = []
                self.stack_space = 0
                for i in program:
                    instruction = self.assign_homes_instr(i, d_var_to_memory)
                    l_inst.append(instruction)
                x86program = X86Program(l_inst)

                # bue: how to add an ast field? am going instance global!
                self.i_spilled = len(e_var_spilled)
                self.used_callee = list(set(d_var_to_color.keys()).intersection(e_reg_callee_saved))
                print('spilled and callee:', self.i_spilled, self.used_callee)

            case _:
                raise Exception('Error: Compiler.assign_homes case not yet implemented.')

        print('ALLOCATE_REGISTERS OUTPUT X86Program:', x86program)
        return x86program


    def assign_homes(self, p: X86Program) -> X86Program:
        print('ASSIGN_HOMES INPUT X86Program:', p)
        x86program = None
        match p:
            case X86Program(program):
                # graph coloring
                live_after, variables = self.uncover_live(p)
                graphi = self.build_interference(p, live_after)
                graphm = self.build_movegraph(p)
                x86program = self.allocate_registers(p, graphi, graphm, variables)

            case _:
                raise Exception('Error: Compiler.assign_homes case not yet implemented.')

        print('ASSIGN_HOMES OUTPUT X86Program:', x86program)
        return x86program


    ############################################################################
    # Patch Instructions: x86var -> x86int
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        print('PATCH_INSTR INPUT instr:', i)
        l_inst = []

        match i:
            case Instr('movq', [mem1, mem2]):
                if mem1 != mem2:  # jump over trivial moves
                    match i:
                        case Instr('movq', [Deref(reg1, arg1), Deref(reg2, arg2)]):
                            l_inst.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                            l_inst.append( Instr('movq', [Reg('rax'), Deref(reg2, arg2)]) )
                        case _:
                            l_inst.append(i)

            case Instr('subq', [Deref(reg1, arg1), Deref(reg2, arg2)]):
                l_inst.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                l_inst.append( Instr('subq', [Reg('rax'), Deref(reg2, arg2)]) )

            case Instr('addq', [Deref(reg1, arg1), Deref(reg2, arg2)]):
                l_inst.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                l_inst.append( Instr('addq', [Reg('rax'), Deref(reg2, arg2)]) )

            case Instr('cmpq',[Immediate(value1),Immediate(value2)]):
                l_inst.append( Instr('movq',[Immediate(value2),Reg('rax')]) )

            case Instr('cmpq',[Deref(reg1,value1),Deref(reg2,value2)]):
                l_inst.append( Instr('movq',[Deref(reg1,value1),Reg('rax')]) )
                l_inst.append( Instr('cmpq', [Reg('rax'),Deref(reg2,value2)]) )

            case Instr('movbzq',[arg,value]):
                if type(value) != Reg():
                    l_inst.append( Instr('movq',[value,Reg('rax')]) )
                    l_inst.append( Instr('movbzq', [arg,Reg('rax')]) )

            case Instr(command, [Immediate(arg1), Deref(reg2, arg2)]):  # big int
                if arg1 >= 2**16:
                    l_inst.append( Instr(command, [Immediate(arg1), Reg('rax')]) )
                    l_inst.append( Instr(command, [Reg('rax'), Deref(reg2, arg2)]) )
                else:
                    l_inst.append(i)

            case Instr(command, [Deref(reg1, arg1), Immediate(arg2)]):  # big int
                if arg2 >= 2**16:
                    l_inst.append( Instr(command, [Immediate(arg2), Reg('rax')]) )
                    l_inst.append( Instr(command, [Reg('rax'), Deref(reg1, arg1)]) )
                else:
                    l_inst.append(i)

            case _:
                l_inst.append(i)

        print('PATCH_INSTR OUTPUT instr:', l_inst)
        return l_inst


    def patch_instructions(self, p: X86Program) -> X86Program:
        print('PATCH_INSTRUCTIONS INPUT X86Program:', p)
        x86program = None

        match p:
            case X86Program(program):
                l_inst = []
                for i in program:
                    l_inst.extend(self.patch_instr(i))
                x86program = X86Program(l_inst)

            case _:
                raise Exception('Error: Compiler.patch_instructions case not yet implemented.')

        print('PATCH_INSTRUCTIONS OUTPUT X86Program:', x86program)
        return x86program


    ############################################################################
    # Prelude & Conclusion: x86int -> x86int
    ############################################################################
    # trip to x86 chapter 1 and 2 section 2.8 generate prelude and conclusion.

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        print('PRELUDE_AND_CONCLUSION INPUT X86Program:', p)
        x86program = None

        match p:
            case X86Program(prog):
                # calculate memory need
                frame_space = align(
                    n = 8 * (self.i_spilled + len(self.used_callee)),
                    alignment = 16
                )

                prelude = [
                    # stor base pointer
                    Instr('pushq', [Reg('rbp')]),
                    # reserve memory
                    Instr('movq', [Reg('rsp'), Reg('rbp')]),
                    Instr('subq', [Immediate(frame_space), Reg('rsp')]),
                ]
                for n, register in enumerate(self.used_callee):
                    # stor callee saved register
                    prelude.append(
                        Instr('movq', [register,  Deref('rbp', - frame_space + ((n + 1) * 8 ))])
                    )

                conclusion = []
                for n, register in enumerate(self.used_callee):
                    # recall callee saved register
                    conclusion.append(
                        Instr('movq', [Deref('rbp', -frame_space + ((n + 1) * 8 )), register])
                    )
                conclusion.extend([
                    # free memory
                    Instr('addq', [Immediate(frame_space), Reg('rsp')]),
                    # recall base pointer
                    Instr('popq', [Reg('rbp')]),
                    # retun ctrl to os
                    Instr('retq', []),
                ])

                # main and conclusion jump. BUE! thsi is not ok yet!
                self.create_block()

                x86program = X86Program(prelude + prog + conclusion)

            case _:
                raise Exception('Error: Compiler.prelude_and_conclusion case not yet implemented.')

        print('PRELUDE_AND_CONCLUSION OUTPUT X86Program:', x86program)
        return x86program

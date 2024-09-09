import ast
from ast import *  # Add, BinOP, Call, Constant, expr, Name, Sub, UnaryOP, USub
from utils import *  # generate_name, input_int, label_name
from x86_ast import *  # X86Program
import os
from typing import List, Tuple, Set, Dict

Binding = Tuple[Name, expr]
Temporaries = List[Binding]


class Compiler:

    ############################################################################
    # Remove Complex Operands: Lvar -> Lvar mon
    ############################################################################

    def rco_exp(self, e: expr, need_atomic : bool) -> Tuple[expr, Temporaries]:
        print('RCO_EXP INPUT expr need_atomic :', e, need_atomic)
        match e:
            case Constant(value):  # Lint leaf
                constant = Constant(value)
                print('RCO_EXP OUTPUT:', constant, [])
                return (constant, []) # expression and enviroment (expr, [(Name, (expr, [(Name, expr)]))])

            case Call(Name('input_int'), []):  # Lint leaf
                #if need_atomic:
                #else:
                #return (e, [])
                pass

            case UnaryOp(USub(), operand):  # Lint complex: operator, operand
                #tmp = Name(generate_name('tmp')
                #return neg64(interp_exp(operand)
                pass

            case BinOp(left, Add(), right):  # Lint comple: expr, operator, expr
                #l = interp_exp(left)
                #r = interp_exp(right)
                #return add64(l, r)
                pass

            case BinOp(left, Sub(), right):  # Lint complex: expr, operator, expr
                #l = interp_exp(left)
                #r = interp_exp(right)
                #return sub64(l, r)
                pass

            case Name(var):  # Lvar
                name = Name(var)
                return name

            case _:
                raise Exception('Error: Compiler.rco_exp case not yet implemented.')

    def rco_stmt(self, s: stmt) -> List[stmt]:
        print('RCO_STMT INPUT stmt:', ast.dump(s))
        match s:
            case Expr(Call(Name('print'), [exp])):  # Lint
                (atm, l_tmp) =  self.rco_exp(exp, True)
                l_stmt = [Expr(Call(Name('print'), [atm]))]
                #l_stmt = [Assign([varc], expc) for varc, expc in l_tmp] + [Expr(Call(Name('print'), [atm]))]
                print('RCO_STMT OUTPUT print l_stmt:', l_stmt)
                return l_stmt

            case Expr(exp):  # Lint
                (atm, l_tmp) =  self.rco_exp(exp, False)  # output: expression and enviroment
                l_stmt = [Assign([atm])]
                print('RCO_STMT OUTPUT Expr l_stmt:', l_stmt)
                return l_stmt

            case Assign([Name(var)], exp):  # Lvar
                (atm, l_tmp) =  self.rco_exp(exp, False)  # output: expression and enviroment
                l_stmt =  [Assign([varc], expc) for varc, expc in l_tmp] + [Assign([Name(var)], atm)]
                print('RCO_STMT OUTPUT Assign l_stmt:', l_stmt)
                return l_stmt

            case _:
                raise Exception('Error: Compiler.rco_stmt case not yet implemented.')

    def remove_complex_operands(self, p: Module) -> Module:
        print('RCO INPUT Module:', ast.dump(p))
        match p:
            case Module(body):  # Lvar
                l_stmt = [self.rco_stmt(stmt) for stmt in body]
                #module = Module(l_stmt)
                module = Module(sum(l_stmt, []))  # bue: what is this sum doing?!
                print('RCO OUTPUT Module:', ast.dump(module))
                return module

            case _:
                raise Exception('Error: Compiler.remove_complex_operands case not yet implemented.')

    ############################################################################
    # Select Instructions: Lvar mon -> x86var
    ############################################################################

    def select_arg(self, e: expr) -> arg:  # arg non terminal  
        print('SELECT_ARG INPUT:', e)
        match e:
            case Constant(var):  # Lint atom
                immediate = Immediate(var)
                return immediate

            case Name(var):  # Lvar atom (arg non terminal)
                name = Name(var)
                return name

            case Call(Name('input_int'), []):  # Lint  expr
                pass

            case _:
                 raise Exception('Error: Compiler.select_arg case not yet implemented.')

    def select_stmt(self, s: stmt) -> List[instr]:  # for stmt non terminal
        print('SELECT_STMT INPUT:', s)
        match s:
            case Expr(Call(Name('print'), [exp])):  # Lint stmt
                arg1 = self.select_arg(exp)
                #print("arg1",arg1)
                fin = Instr('movq',[arg1,Reg('rdi')])
                res = Callq(label_name('print_int'),arg1)
                l_instr = []
                return l_instr

            case Expr(exp):  # Lint stmt
                l_instr = [self.select_arg(exp)]
                return l_instr

            case Assign([Name(var)], exp):  # Lvar stmt
                pass


            case UnaryOp(USub(), operand):  # Lint expr : exproperator, operand
                pass

            case BinOp(left, Add(), right):  # Lint expr: expr, operator, expr
                #l_instrct = []
                #l_instrct.append(
                #instct = Instr('movq', [arg1, Reg('rax')])
                pass
                  
            case BinOp(left, Sub(), right):  # Lint expr: expr, operator, expr
                pass

            case _:
                 raise Exception('Error: Compiler.select_stmt case not yet implemented.')

    def select_instructions(self, p: Module) -> X86Program:
        print('SELECT_INSTRUCTIONS INPUT:', p)
        match p:
            case Module(body):
                l_instr = [self.select_stmt(stmt) for stmt in body]
                x86program = X86Program(sum(l_instr, []))
                print('SELECT_INSTRUCTIONS INPUT:', x86program)
                return x86program

            case _:
                raise Exception('Error: Compiler.select_instructions case not yet implemented.')

    ############################################################################
    # Assign Homes: x86var -> x86var
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        print('ASSIGN_HOMES_ARG arg home:', a, home)
        # YOUR CODE HERE
        pass

    def assign_homes_instr(self, i: instr, home: Dict[Variable, arg]) -> instr:
        print('ASSIGN_HOMES_INSTR instr home:', i, home)
        # YOUR CODE HERE
        pass

    def assign_homes(self, p: X86Program) -> X86Program:
        print('ASSIGN_HOMES X86Program:', p)
        # YOUR CODE HERE
        pass

    ############################################################################
    # Patch Instructions: x86var -> x86int
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        print('PATCH_INSTR instr:', i)
        # YOUR CODE HERE
        pass

    def patch_instructions(self, p: X86Program) -> X86Program:
        print('PATCH_INSTRUCTIONS X86Program:', p)
        # YOUR CODE HERE
        pass

    ############################################################################
    # Prelude & Conclusion: x86int -> x86int
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        print('PRELUDE_AND_CONCLUSION X86Program:', p)
        # YOUR CODE HERE
        pass


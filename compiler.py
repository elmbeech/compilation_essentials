import ast
from ast import *  # Add, BinOP, Call, Constant, expr, Name, Sub, UnaryOP, USub
# https://docs.python.org/3/library/language.html
# https://docs.python.org/3/library/ast.html
# https://greentreesnakes.readthedocs.io/en/latest/
from utils import *  # generate_name, input_int, label_name
from x86_ast import *  # arg, Callq, Deref, Immediate, Instr, Jump, Reg, Retq, Variable, X86Program
import os
from typing import List, Tuple, Set, Dict
from graph import UndirectedAdjList

Binding = Tuple[Name, expr]
Temporaries = List[Binding]

# functions
def pe_neg(r):
    '''
    partial evaluator function for lvar fig 1.5 and section2.9.
    '''
    match r:
        case Constant(n):  # Lint
            return Constant(neg64(n))

        case _:  # Lint
            return UnaryOp(USub(), r)  # Lint

def pe_add(r1, r2):
    '''
    partial evaluator function for lvar fig 1.5 and section 2.9.
    '''
    match (r1, r2):
        case (Constant(n1),Constant(n2)):  # Lint
            return Constant(add64(n1, n2))

        case _:  # Lint
            return BinOp(r1, Add(), r2)

def pe_sub(r1, r2):
    '''
    partial evaluator function for lvar fig 1.5 and section 2.9.
    '''
    match (r1, r2):
        case (Constant(n1), Constant(n2)):  # Lint
            return Constant(sub64(n1, n2))

        case _:  # Lint
            return BinOp(r1, Sub(), r2)

def pe_exp(e):
    '''
    partial evaluator function for lvar fig 1.5 and section 2.9.
    '''
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
    '''
    partial evaluator function for lvar fig 1.5 and section 2.9.
    '''
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
    '''
    partial evaluator function for lvar fig 1.5 and section 2.9.
    '''
    match p:
        case Module(body):  # Lint
            new_body = [pe_stmt(s) for s in body]
            return Module(new_body)

        case _:
            raise Exception('Error: pe_P_int case not yet implemented.')



# classes

class Compiler:

    ############################################################################
    # Remove Complex Operands: Lvar -> Lvar mon
    ############################################################################

    def big_constant(self, value: int):
        if value >= 2**16:
            value = value % 2**16
        return value

    def rco_exp(self, e: expr, need_atomic : bool) -> Tuple[expr, Temporaries]:
        '''
        trip to x86 chapter 1 and 2 section 2.4 remove compex operands.
        output: expression and enviroment (expr, [(Name, (expr, [(Name, expr)]))])
        '''
        print('RCO_EXP INPUT expr need_atomic :', e, need_atomic)
        match e:
            case Constant(value):  # Lint; always leaf
                value = self.big_constant(value)
                constant = Constant(value)
                print('RCO_EXP OUTPUT constant atom:', (constant, []))
                return (constant, [])

            case Call(Name('input_int'), []):  # Lint; always leaf
                inputint = Call(Name('input_int'), [])
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    print('RCO_EXP OUTPUT input_int complex:', (tmp, [(tmp, inputint)]))
                    return (tmp, [(tmp, inputint)])
                print('RCO_EXP OUTPUT input_int atom:', (inputint, []))
                return (inputint, [])

            case UnaryOp(USub(), operand):  # Lint; maybe complex; operator, operand
                newexp, l_tmp = self.rco_exp(operand, True)
                neg = UnaryOp(USub(), newexp)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    print('RCO_EXP OUTPUT neg complex:', (tmp, l_tmp + [(tmp, neg)]))
                    return (tmp, l_tmp + [(tmp, neg)])
                print('RCO_EXP OUTPUT neg atom:', (neg, l_tmp))
                return (neg, l_tmp)

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

            case Name(var):  # Lvar
                name = Name(var)
                print('RCO_EXP OUTPUT var name atom:', (name, []))
                return (name, [])

            case _:
                raise Exception('Error: Compiler.rco_exp case not yet implemented.')

    def rco_stmt(self, s: stmt) -> List[stmt]:
        '''
        trip to x86 chapter 1 and 2 section 2.4 remove compex operands.
        '''
        print('RCO_STMT INPUT stmt:', ast.dump(s))
        match s:
            case Expr(Call(Name('print'), [exp])):  # Lint
                newexp, l_tmp =  self.rco_exp(exp, True)
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmp] + [Expr(Call(Name('print'), [newexp]))]
                print('RCO_STMT OUTPUT print:', l_stmt)
                return l_stmt

            case Expr(exp):  # Lint
                newexp, l_tmp =  self.rco_exp(exp, False)  # output: expression and enviroment
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmp]
                print('RCO_STMT OUTPUT expr:', l_stmt)
                return l_stmt

            case Assign([Name(var)], exp):  # Lvar
                newexp, l_tmp =  self.rco_exp(exp, False)  # output: expression and enviroment
                l_stmt =  [Assign([varc], expc) for varc, expc in l_tmp] + [Assign([Name(var)], newexp)]
                print('RCO_STMT OUTPUT assign:', l_stmt)
                return l_stmt

            case Expr(Call(Name('inpt_int'), [exp])):  # Lvar
                newexp, l_tmp = self.rco_exp(exp, True)
                return [Assign([varc], expc) for varc, expc in l_tmp]

            case _:
                raise Exception('Error: Compiler.rco_stmt case not yet implemented.')

    def remove_complex_operands(self, p: Module) -> Module:
        '''
        trip to x86 chapter 1 and 2 section 2.4 remove compex operands.
        '''
        print('RCO INPUT Module:', ast.dump(p))
        match p:
            case Module(body):  # Lint
                l_stmt = []
                for stmt in body:
                    l_stmt.extend(self.rco_stmt(stmt))
                module = Module(l_stmt)
                #ll_stmt = [self.rco_stmt(stmt) for stmt in body]
                #module = Module(sum(ll_stmt, []))  # bue: what is this sum doing?!
                print('RCO OUTPUT module:', ast.dump(module))
                return module

            case _:
                raise Exception('Error: Compiler.remove_complex_operands case not yet implemented.')

    ############################################################################
    # Select Instructions: Lvar mon -> x86var
    ############################################################################

    def select_arg(self, e: expr) -> arg:  # arg terminal
        '''
        trip to x86 chapter 1 and 2 section 2.5 select instructions.
        '''
        # work on atoms
        print('SELECT_ARG INPUT:', e)
        match e:
            case Constant(var):  # Lint atom
                arg_var = Immediate(var)
                print('SELECT_ARG OUTPUT constant:', arg_var)
                return arg_var

            case Name(var):  # Lvar atom
                arg_var = Variable(var)
                print('SELECT_ARG OUTPUT var name:', arg_var)
                return arg_var

            case _:
                raise Exception('Error: Compiler.select_arg case not yet implemented.')

    def select_stmt(self, s: stmt) -> List[instr]:  # stmt non terminal
        '''
        trip to x86 chapter 1 and 2 section 2.5 select instructions.
        '''
        # workhorse
        print('SELECT_STMT INPUT:', s)
        match s:
            case Assign([Name(var)], Call(Name('input_int'), [])):  # Lint  expr
                arg_var = self.select_arg(Name(var))
                l_instr = [
                    Callq(label_name('read_int'), []),
                    Instr('movq', [Reg('rax'), arg_var]),
                ]
                print('SELECT_STMT OUTPUT input_int:', l_instr)
                return l_instr

            case Assign([Name(var)], UnaryOp(USub(), operand)):  # Lint expr : exproperator, operand
                arg_var = self.select_arg(Name(var))
                arg_operand = self.select_arg(operand)
                l_instr = [
                    Instr('movq', [arg_operand, Reg('rax')]),
                    Instr('negq', [Reg('rax')]),
                    Instr('movq', [Reg('rax'), arg_var]),
                ]
                print('SELECT_STMT OUTPUT neg:', l_instr)
                return l_instr

            case Assign([Name(var)], BinOp(left, Add(), right)):  # Lint expr: expr, operator, expr
                arg_var = self.select_arg(Name(var))
                arg_left = self.select_arg(left)
                arg_right = self.select_arg(right)
                if arg_left == arg_right:
                    l_instr = [
                        Instr('addq', [arg_left, arg_var]),
                    ]
                else:
                    l_instr = [
                        Instr('movq', [arg_left, arg_var]),
                        Instr('addq', [arg_right, arg_var]),
                    ]
                print('SELECT_STMT OUTPUT add:', l_instr)
                return l_instr

            case Assign([Name(var)], BinOp(left, Sub(), right)):  # Lint expr: expr, operator, expr
                arg_var = self.select_arg(Name(var))
                arg_left = self.select_arg(left)
                arg_right = self.select_arg(right)
                l_instr = [
                    Instr('movq', [arg_left, Reg('rax')]),
                    Instr('subq', [arg_right, Reg('rax')]),
                    Instr('movq', [Reg('rax'), arg_var]),
                ]
                print('SELECT_STMT OUTPUT sub:', l_instr)
                return l_instr

            case Expr(Call(Name('print'), [exp])):  # Lint stmt
                arg_exp = self.select_arg(exp)
                l_instr = [
                    Instr('movq', [arg_exp, Reg('rdi')]),
                    Callq(label_name('print_int'), arg_exp),
                ]
                # BUE: is this arg_exp correct?!
                print('SELECT_STMT OUTPUT print:', l_instr)
                return l_instr

            # bue: is terminal. resolved on the select_instructions level.
            #case Expr(exp):  # Lint stmt
            #    arg_exp = self.select_arg(exp)
            #    l_instr = []
            #    l_instr.append( )
            #    print('SELECT_STMT OUTPUT exp:', l_instr)
            #    return l_instr

            case Assign([Name(var)], exp):  # Lvar stmt
                arg = self.select_arg(exp)
                l_instr = [
                    Instr('movq', [arg, Variable(var)]),
                ]
                print('SELECT_STMT OUTPUT var name:', l_instr)
                return l_instr

            case _:
                 raise Exception('Error: Compiler.select_stmt case not yet implemented.')

    def select_instructions(self, p: Module) -> X86Program:
        '''
        trip to x86 chapter 1 and 2 section 2.5 select instructions.
        '''
        print('SELECT_INSTRUCTIONS INPUT:', ast.dump(p))
        match p:
            case Module(body):
                l_instr = [self.select_stmt(stmt) for stmt in body]
                x86program = X86Program(sum(l_instr, []))
                #x86program = []
                #for stmt in body:
                #    instruction = self.select_stmt(stmt)
                #    x86program.extend(instruction)
                print('SELECT_INSTRUCTIONS OUTPUT x86program:', x86program, type(x86program))
                return x86program

            case _:
                raise Exception('Error: Compiler.select_instructions case not yet implemented.')


    ###########################################################################
    # Uncover Live
    ###########################################################################

    def read_vars(self, i: instr) -> Set[location]:

        # YOUR CODE HERE
        pass

    def write_vars(self, i: instr) -> Set[location]:
        # YOUR CODE HERE
        self.read_vars
        pass

    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        print('UNCOVER_LIVE INPUT:', ast.dump(p))
        match p:
            case Module(body):
                l_instr = [self.select_stmt(stmt) for stmt in body]
                self.write_vars()
                x86program = X86Program(sum(l_instr, []))
                #x86program = []
                #for stmt in body:
                #    instruction = self.select_stmt(stmt)
                #    x86program.extend(instruction)
                print('UNCOVER_LIVE OUTPUT x86program:', x86program, type(x86program,))
                return x86program

            case _:
                raise Exception('Error: Compiler.select_instructions case not yet implemented.')


    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program, live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Allocate Registers
    ############################################################################

    # Returns the coloring and the set of spilled variables.
    def color_graph(self, graph: UndirectedAdjList, variables: Set[location]) -> Tuple[Dict[location, int], Set[location]]:
        # YOUR CODE HERE
        pass

    def allocate_registers(self, p: X86Program, graph: UndirectedAdjList) -> X86Program:
        # YOUR CODE HERE
        pass





    ############################################################################
    # Assign Homes: x86var -> x86var
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        '''
        trip to x86 chapter 1 and 2 section 2.6 assign homes.
        '''
        print('ASSIGN_HOMES_ARG INPUT arg home:', a, home)
        argument = None

        match a:
            case Variable(arg):
                if not (Variable(arg) in home.keys()):
                    self.stack_space -= 8
                    home.update({Variable(arg): Deref('rbp', self.stack_space)})
                argument = home[Variable(arg)]
                print('ASSIGN_HOMES_ARG OUTPUT arg:', argument, home)
                return argument

            case _:
                raise Exception('Error: Compiler.assign_homes_arg case not yet implemented.')

    def assign_homes_instr(self, i: instr, home: Dict[Variable, arg]) -> instr:
        '''
        trip to x86 chapter 1 and 2 section 2.6 assign homes.
        '''
        print('ASSIGN_HOMES_INSTR INPUT instr home:', i, home)
        instruction = None

        # Immediate, Reg, Variable: 3**2 = 9 [cases]
        match i:
            case Instr(command, [Immediate(arg1), Immediate(arg2)]):  # ii
                instruction = i

            case Instr(command, [Immediate(arg1), Reg(arg2)]):  # ir
                instruction = i

            case Instr(command, [Immediate(arg1), Variable(arg2)]):  # iv
                arg_var2 = self.assign_homes_arg(Variable(arg2), home)
                instruction = Instr(command, [Immediate(arg1), arg_var2])

            case Instr(command, [Reg(arg1), Immediate(arg2)]):  # ri
                instruction = i

            case Instr(command, [Reg(arg1), Reg(arg2)]):  # rr
                instruction = i

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

            case Callq('print_int', []):  # other
                instruction = i

            case _:
                instruction = i

                # BUE: have to be fixed!
                #raise Exception('Error: Compiler.assign_homes_instr case not yet implemented.')

        print('ASSIGN_HOMES_INSTR OUTPUT instr, home:' , instruction, home)
        return instruction

    def assign_homes(self, p: X86Program) -> X86Program:
        '''
        trip to x86 chapter 1 and 2 section 2.6 assign homes.
        '''
        print('ASSIGN_HOMES INPUT X86Program:', p)
        x86program = None

        match p:
            case X86Program(program):
                l_instr = []
                d_home = {}
                #d_home = self.collect_instr(body)
                self.stack_space = 0
                for i in program:
                    instruction = self.assign_homes_instr(i, d_home)
                    l_instr.append(instruction)
                x86program = X86Program(l_instr)
                print('ASSIGN_HOMES OUTPUT X86Program:', x86program)
                return x86program

            case _:
                raise Exception('Error: Compiler.assign_homes case not yet implemented.')


    ############################################################################
    # Patch Instructions: x86var -> x86int
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        print('PATCH_INSTR INPUT instr:', i)
        l_instr = []

        match i:
            case Instr('movq', [Deref(reg1, arg1), Deref(reg2, arg2)]):
                #self.pop = True
                l_instr.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                l_instr.append( Instr('movq', [Reg('rax'), Deref(reg2, arg2)]) )

            case Instr('subq', [Deref(reg1, arg1), Deref(reg2, arg2)]):
                #self.pop = True
                l_instr.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                l_instr.append( Instr('subq', [Reg('rax'), Deref(reg2, arg2)]) )

            case Instr('addq', [Deref(reg1, arg1), Deref(reg2,arg2)]):
                #self.pop = True
                l_instr.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                l_instr.append( Instr('addq', [Reg('rax'), Deref(reg2, arg2)]) )

            case _:
                l_instr.append(i)

        print('PATCH_INSTR OUTPUT instr:', l_instr)
        return l_instr

    def patch_instructions(self, p: X86Program) -> X86Program:
        print('PATCH_INSTRUCTIONS INPUT X86Program:', p)

        match p:
            case X86Program(program):
                l_instr = []
                #self.pop = False
                for i in program:
                    l_instruction = self.patch_instr(i)
                    #if self.pop:
                    #    l_instr.pop(-1)
                    #    self.pop = False
                    l_instr.extend(l_instruction)
                x86program = X86Program(l_instr)
                print('PATCH_INSTRUCTIONS OUTPUT X86Program:', x86program)
                return x86program
                # BUE: pop has to be fixed!

            case _:
                raise Exception('Error: Compiler.patch_instructions case not yet implemented.')


    ############################################################################
    # Prelude & Conclusion: x86int -> x86int
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        '''
        trip to x86 chapter 1 and 2 section 2.8 generate prelude and conclusion.
        '''
        print('PRELUDE_AND_CONCLUSION INPUT X86Program:', p)

        match p:
            case X86Program(prog):
                frame_space = align(n = -(self.stack_space), alignment=16 )
                prelude = [
                    Instr('pushq', [Reg('rbp')]),
                    Instr('movq', [Reg('rsp'), Reg('rbp')]),
                    Instr('subq', [Immediate(frame_space), Reg('rsp')]),
                ]
                conclusion = [
                    Instr('addq', [Immediate(frame_space), Reg('rsp')]),
                    Instr('popq', [Reg('rbp')]),
                    Instr('retq', []),
                ]
                x86program = X86Program(prelude + prog + conclusion)
                print('PRELUDE_AND_CONCLUSION OUTPUT X86Program:', x86program)
                return x86program

            case _:
                raise Exception('Error: Compiler.prelude_and_conclusion case not yet implemented.')


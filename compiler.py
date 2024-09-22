
# libraries
import ast
from ast import *  # Add, BinOP, Call, Constant, expr, Name, Sub, UnaryOP, USub
# https://docs.python.org/3/library/language.html
# https://docs.python.org/3/library/ast.html
# https://greentreesnakes.readthedocs.io/en/latest/
from graph import UndirectedAdjList
import os
from utils import *  # generate_name, input_int, label_name
from x86_ast import *  # arg, Callq, Deref, Immediate, Instr, Jump, Reg, Retq, Variable, X86Program

from priority_queue import PriorityQueue

# types
from typing import List, Tuple, Set, Dict
Binding = Tuple[Name, expr]
Temporaries = List[Binding]


# const

# section 4.1 register calling convention
l_func = [Reg('rdi'), Reg('rsi'), Reg('rdx'), Reg('rcx'), Reg('r8'), Reg('r9')]

e_caller_saved = set(l_func).union({Reg('rax'), Reg('r10'), Reg('r11')})

e_callee_saved = {
    Reg('rsp'), Reg('rbp'), Reg('rbx'),
    Reg('r12'), Reg('r13'), Reg('r14'), Reg('r15'),
}

color_map = {
    0 : Reg('rcx'), 1 : Reg('rdx'), 2 : Reg('rsi'), 3: Reg('rdi'),
    4 : Reg('r8'), 5 : Reg('r9'), 6 : Reg('r10'), 7 : Reg('rbx'),
    8 : Reg('r12'), 9 : Reg('r13'), 10 : Reg('14'),
}

non_color = {
    Reg('rax') : -1, Reg('rsp') : -2, Reg('rbp') : -3, Reg('r11') : -4,
    Reg('r15') : -5,
}


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


    def rco_exp(self, e: expr, need_atomic : bool) -> Tuple[expr, Temporaries]:
        '''
        trip to x86 chapter 1 and 2 section 2.4 remove compex operands.
        output: expression and enviroment (expr, [(Name, (expr, [(Name, expr)]))])
        '''
        print('RCO_EXP INPUT expr need_atomic :', e, need_atomic)
        match e:
            case Constant(value):  # Lint; always leaf
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

            case UnaryOp(USub(), operand):  # Lint and Lvar; maybe complex; operator, operand
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

            case Name(var):  # Lvar; always leaf
                name = Name(var)
                print('RCO_EXP OUTPUT var name atom:', (name, []))
                return (name, [])

            case _:
                raise Exception('Error: Compiler.rco_exp case not yet implemented.')


    def rco_stmt(self, s: stmt) -> List[stmt]:
        '''
        trip to x86 chapter 1 and 2 section 2.4 remove complex operands.
        '''
        print('RCO_STMT INPUT stmt:', ast.dump(s))
        l_stmt = None

        match s:
            case Expr(Call(Name('print'), [exp])):  # Lint
                newexp, l_tmp =  self.rco_exp(exp, True)
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmp] + [Expr(Call(Name('print'), [newexp]))]

            case Expr(exp):  # Lint
                newexp, l_tmp =  self.rco_exp(exp, False)  # output: expression and enviroment
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmp]

            case Assign([Name(var)], exp):  # Lvar
                newexp, l_tmp =  self.rco_exp(exp, False)  # output: expression and enviroment
                l_stmt =  [Assign([varc], expc) for varc, expc in l_tmp] + [Assign([Name(var)], newexp)]

            case Expr(Call(Name('inpt_int'), [exp])):  # Lvar
                newexp, l_tmp = self.rco_exp(exp, True)
                l_stmt = [Assign([varc], expc) for varc, expc in l_tmp]

            case _:
                raise Exception('Error: Compiler.rco_stmt case not yet implemented.')

        print('RCO_STMT OUTPUT l_stmt:', l_stmt)
        return l_stmt


    def remove_complex_operands(self, p: Module) -> Module:
        '''
        trip to x86 chapter 1 and 2 section 2.4 remove compex operands.
        '''
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


    ############################################################################
    # Select Instructions: Lvar mon -> x86var
    ############################################################################


    def select_arg(self, e: expr) -> arg:  # arg terminal
        '''
        trip to x86 chapter 1 and 2 section 2.5 select instructions.
        '''
        # work on atoms
        print('SELECT_ARG INPUT expr:', e)
        arg_var = None

        match e:
            case Constant(var):  # Lint atom
                arg_var = Immediate(var)

            case Name(var):  # Lvar atom
                arg_var = Variable(var)

            case _:
                raise Exception('Error: Compiler.select_arg case not yet implemented.')

        print('SELECT_ARG OUTPUT arg:', arg_var)
        return arg_var


    def select_stmt(self, s: stmt) -> List[instr]:  # stmt non terminal
        '''
        trip to x86 chapter 1 and 2 section 2.5 select instructions.
        '''
        print('SELECT_STMT INPUT stmt:', s)
        l_inst = None

        match s:
            case Assign([Name(var)], Call(Name('input_int'), [])):  # Lint  expr
                arg_var = self.select_arg(Name(var))
                l_inst = [
                    Callq(label_name('read_int'), []),
                    Instr('movq', [Reg('rax'), arg_var]),
                ]

            case Assign([Name(var)], UnaryOp(USub(), operand)):  # Lint expr : exproperator, operand
                arg_var = self.select_arg(Name(var))
                arg_operand = self.select_arg(operand)
                l_inst = [
                    Instr('movq', [arg_operand, Reg('rax')]),
                    Instr('negq', [Reg('rax')]),
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

            case Assign([Name(var)], exp):  # Lvar stmt
                arg = self.select_arg(exp)
                l_inst = [
                    Instr('movq', [arg, Variable(var)]),
                ]

            case _:
                 raise Exception('Error: Compiler.select_stmt case not yet implemented.')

        print('SELECT_STMT OUTPUT l_inst:', l_inst)
        return l_inst


    def select_instructions(self, p: Module) -> X86Program:
        '''
        trip to x86 chapter 1 and 2 section 2.5 select instructions.
        '''
        print('SELECT_INSTRUCTIONS INPUT Module:', ast.dump(p))
        x86program = None

        match p:
            case Module(body):
                l_inst = []
                for stmt in body:
                    l_inst.extend(self.select_stmt(stmt))
                x86program = X86Program(l_inst)

            case _:
                raise Exception('Error: Compiler.select_instructions case not yet implemented.')

        print('SELECT_INSTRUCTIONS OUTPUT x86program:', x86program)
        return x86program


    ###########################################################################
    # Uncover Live
    ###########################################################################

    def read_vars(self, i: instr) -> Set[location]:
        '''
        register allocation chapter 2 section 4.2 liveness analysis
        '''
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
            case Callq('print', value):  # read form e_caller_saved register
                #if value > len(e_callee_saved):
                #    raise Exception(f'Error: Compiler.read_vars callq case for functions with > {len(e_callee_saved)} arguments not yet implemented.')
                #for reg in e_callee_saved:
                #   e_read.add(reg)
                e_read.add(Reg('rdi'))

            case _:
                pass

        print('READ_VARS OUTPUT:', e_read)
        return e_read


    def write_vars(self, i: instr) -> Set[location]:
        '''
        register allocation chapter 2 section 4.2 liveness analysis
        '''
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
            case Callq('read_int', value):  # write in e_caller_saved registers
                if value > len(l_func):
                    raise Exception(f'Error: Compiler.write_vars callq case for functions with > {len(l_func)} arguments not yet implemented.')
                for n in range(value):
                    e_write.add(Reg(l_func[n]))

            case _:
                pass

        print('WRITE_VARS OUTPUT:', e_write)
        return(e_write)


    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        '''
        register allocation chapter 2 section 4.2 liveness analysis
        '''
        print('UNCOVER_LIVE INPUT:', p)
        d_after = None

        match p:
            case X86Program(body):
                d_after = {}
                e_after = set()
                for i in body[::-1]:
                     e_read = self.read_vars(i)
                     e_write = self.write_vars(i)
                     e_before = (e_after.difference(e_write)).union(e_read)
                     d_after.update({i: e_after})
                     e_after = e_before
                     #e_location = e_read.union(e_write)

            case _:
                raise Exception('Error: Compiler.select_instructions case not yet implemented.')

        print('UNCOVER_LIVE OUTPU dict:', d_after)
        return d_after


    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program, live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        '''
        register allocation chapter 2 section 4.3 build the interference graph
        '''
        print('BUILD_INTERFERENCE INPUT:', p)
        g = None

        match p:
            case X86Program(body):

                g = UndirectedAdjList()
                for i in body:
                    match i:
                        case Callq(command, []):  # bue: print read_int
                            for dst in e_caller_saved:  # bue: why are this not only the l_func ones?
                                for var in live_after[i]:
                                    g.add_edge(dst, var)

                        case Inst('movq', [src, dst]):
                            for var in live_after[i]:
                                if (var != dst) and (var != src):
                                    g.add_edge(dst, var)

                        case _:
                            e_write = self.write_vars(i)
                            for dst in e_write:
                                for var in live_after[i]:
                                    if (var != dst):
                                        g.add_edge(dst, var)

            case _:
                raise Exception('Error: Compiler.build_interference case not yet implemented.')

        print('BUILD_INTERFERENCE OUTPUT:', g.show())
        return g


    ############################################################################
    # Allocate Registers
    ############################################################################

    # Returns the coloring and the set of spilled variables.
    def color_graph(self, graph: UndirectedAdjList, variables: Set[location]) -> Tuple[Dict[location, int], Set[location]]:
        print('COLOR_GRAPH INPUT:')

        # get color inetger
        ei_rainbow = set(color_map.keys())

        # get spilled var set
        eo_spilled = set()

        # extract variable objects from graph
        w = set(graph.vertices())

        # get var color integer mapping
        doi_color = {}
        for o_var in w:
            doi_color.update({o_var : None})

        # get satutration dictionary
        doe_satur = {}
        for o_var in w:
            doe_satur.update({o_var : set()})

        # build priority queue
        def less(x, y):
            return len(doe_satur[x.key]) < len(doe_satur[y.key])
        pqueue = PriorityQueue(less)
        for o_var, e_satur in doe_satur.items():
            pqueue.push(o_var)

        # traverse the graph
        while pqueue.heap.heap_size != 0:
            # pop most saturated value
            o_var = pqueue.pop()

            # get lowest color not adjacent
            # if necessary, update rainbow with spoilled color
            ei_colorpot = ei_rainbow.difference(doe_satur[o_var])
            if len(ei_colorpot) != 0:
                i_color = min(ei_colorpot)
            else:
                i_color = max(ei_rainbow) + 1
                ei_rainbow.add(i_color)

            # update spilled varuiable set
            if i_color >= len(color_map):
                eo_spilled.add(o_var)

            # color variable
            doi_color.update({o_var : i_color})

            # update saturation
            for o_adj in graph.adjacent(o_var):
                doe_satur[o_adj].add(i_color)

        print('COLOR_GRAPH OUTPUT dict coloring and set spilled var:', doi_color, eo_spilled)
        return (doi_color, eo_spilled)


    def allocate_registers(self, p: X86Program, graph: UndirectedAdjList) -> X86Program:
        print('ALLOCATE_REGISTERS INPUT:', ast.dump(p))
        print('ALLOCATE_REGISTERS OUTPUT:')


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

            case _:
                raise Exception('Error: Compiler.assign_homes_arg case not yet implemented.')

        print('ASSIGN_HOMES_ARG OUTPUT arg:', argument)
        return argument


    def assign_homes_instr(self, i: instr, home: Dict[Variable, arg]) -> instr:
        '''
        trip to x86 chapter 1 and 2 section 2.6 assign homes.
        '''
        print('ASSIGN_HOMES_INSTR INPUT instr, home:', i, home)
        instruction = None

        # Immediate, Reg, Variable: 3**2 = 9 [cases]
        # only variables have to be assigned a home
        match i:

            case Instr(command, [Variable(arg)]):  # v
                arg_var1 = self.assign_homes_arg(Variable(arg), home)
                instruction = Instr(command, [arg_var])

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


    def assign_homes(self, p: X86Program) -> X86Program:
        '''
        trip to x86 chapter 1 and 2 section 2.6 assign homes.
        '''
        print('ASSIGN_HOMES INPUT X86Program:', p)
        x86program = None

        match p:
            case X86Program(program):

                # graph coloring register allocation version:
                live_after = self.uncover_live(p)
                graph = self.build_interference(p, live_after)
                #variables = self.(p)
                self.color_graph(graph, set())

                # simple register allocaltion version:
                l_inst = []
                d_home = {}
                #d_home = self.collect_instr(body)
                self.stack_space = 0
                for i in program:
                    instruction = self.assign_homes_instr(i, d_home)
                    l_inst.append(instruction)
                x86program = X86Program(l_inst)

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
            case Instr('movq', [Deref(reg1, arg1), Deref(reg2, arg2)]):
                l_inst.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                l_inst.append( Instr('movq', [Reg('rax'), Deref(reg2, arg2)]) )

            case Instr('subq', [Deref(reg1, arg1), Deref(reg2, arg2)]):
                l_inst.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                l_inst.append( Instr('subq', [Reg('rax'), Deref(reg2, arg2)]) )

            case Instr('addq', [Deref(reg1, arg1), Deref(reg2, arg2)]):
                l_inst.append( Instr('movq', [Deref(reg1, arg1), Reg('rax')]) )
                l_inst.append( Instr('addq', [Reg('rax'), Deref(reg2, arg2)]) )

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


    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        '''
        trip to x86 chapter 1 and 2 section 2.8 generate prelude and conclusion.
        '''
        print('PRELUDE_AND_CONCLUSION INPUT X86Program:', p)
        x86program = None

        match p:
            case X86Program(prog):
                frame_space = align(n = -(self.stack_space), alignment=16)
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

            case _:
                raise Exception('Error: Compiler.prelude_and_conclusion case not yet implemented.')

        print('PRELUDE_AND_CONCLUSION OUTPUT X86Program:', x86program)
        return x86program


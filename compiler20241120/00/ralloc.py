from ast import *
from graph import UndirectedAdjList
from priority_queue import PriorityQueue
import var
from var import Var
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict

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

    
class RegisterAllocator(var.Var):

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
                    variables: Set[location]) -> Tuple[Dict[location, int], Set[location]]:
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

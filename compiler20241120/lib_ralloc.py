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


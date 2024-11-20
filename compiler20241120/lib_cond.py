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


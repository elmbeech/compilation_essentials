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
import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Set, Dict
import interp_Lvar
import type_check_Lvar
from interp_x86.eval_x86 import interp_x86

Binding = tuple[Name, expr]
Temporaries = List[Binding]

class Var:


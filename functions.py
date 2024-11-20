import sys
sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

from ast import *
from math import floor
from utils import *
from x86_ast import *
from var import Temporaries
import tuples
import typing
from typing import List, Dict, Set
from graph import UndirectedAdjList
from register_allocator import registers, registers_for_alloc, callee_save_for_alloc
import type_check_Ltup
import type_check_Ctup
import interp_Ltup
import interp_Ctup
from racket_interp_x86 import *

class Functions(tuples.Tuples):

    ###########################################################################
    # Shrink
    ###########################################################################

    pass

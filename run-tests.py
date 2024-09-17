import argparse
import os
import sys

#sys.path.append('../python-student-support-code')
#sys.path.append('../python-student-support-code/interp_x86')
sys.path.append('../compilation_essentials')
sys.path.append('../compilation_essentials/interp_x86')

import compiler
import interp_Lvar
import type_check_Lvar
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

parser = argparse.ArgumentParser()
parser.add_argument('tpathfile', nargs='?', default='tests/var/zero.py', help='python test file')
args = parser.parse_args()

enable_tracing()

compiler = compiler.Compiler()

typecheck_Lvar = type_check_Lvar.TypeCheckLvar().type_check

typecheck_dict = {
    'source': typecheck_Lvar,
    'remove_complex_operands': typecheck_Lvar,
}
interpLvar = interp_Lvar.InterpLvar().interp
interp_dict = {
    'remove_complex_operands': interpLvar,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

if (args.tpathfile.lower() == 'all'):
    print('*** RUN ALL TESTS! ***')
    run_tests(
        lang = 'var', 
        compiler = compiler, 
        compiler_name = 'var',      
        type_check_dict = typecheck_dict,
        interp_dict = interp_dict,
    )
else:
    print(f'*** RUN TEST {args.tpathfile}! ***')
    run_one_test(
        test = os.getcwd() + f'/{args.tpathfile}',
        lang = 'var',
        compiler = compiler,
        compiler_name = 'var',
        type_check_dict = typecheck_dict,
        interp_dict = interp_dict,
    )

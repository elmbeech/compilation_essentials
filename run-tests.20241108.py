import argparse
import os
import sys

#sys.path.append('../python-student-support-code')
#sys.path.append('../python-student-support-code/interp_x86')
sys.path.append('../compilation_essentials')
sys.path.append('../compilation_essentials/interp_x86')

import compiler
import interp_Ltup, interp_Ctup  # interp_Lvar, interp_Lif, interp_Cif, interp_Lwhile, interp_Ltup, interp_Ctup
import type_check_Ltup, type_check_Ctup # type_check_Lvar, type_check_Lif, type_check_Cif, type_check_Lwhile, type_check_Cwhile, type_check_Ltup, type_check_Ctup
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

parser = argparse.ArgumentParser()
parser.add_argument('tpathfile', nargs='?', default='tests/var/zero.py', help='python test file')
args = parser.parse_args()

enable_tracing()

compiler = compiler.Compiler()


####################
# set type checker #
####################

#typecheck_Lvar = type_check_Lvar.TypeCheckLvar().type_check
#typecheck_Lif = type_check_Lif.TypeCheckLif().type_check
#typecheck_Lwhile = type_check_Lwhile.TypeCheckLwhile().type_check
typecheck_Ltup = type_check_Ltup.TypeCheckLtup().type_check

#typecheck_Cif = type_check_Cif.TypeCheckCif().type_check
#typecheck_Cwhile = type_check_Cwhile.TypeCheckCwhile().type_check
typecheck_Ctup = type_check_Ctup.TypeCheckCtup().type_check

typecheck_dict = {
    #'source': typecheck_Lvar,
    #'source': typecheck_Lif,
    #'source': typecheck_Lwhile,
    'source': typecheck_Ltup,

    #'shrink': typecheck_Lif,
    #'shrink': typecheck_Lwhile,
    'shrink': typecheck_Ltup,

    'expose_allocation': typecheck_Ltup,

    #'remove_complex_operands': typecheck_Lvar,
    #'remove_complex_operands': typecheck_Lif,
    #'remove_complex_operands': typecheck_Lwhile,
    'remove_complex_operands': typecheck_Ltup,

    #'explicate_contol': typecheck_Cif,
    #'explicate_contol': typecheck_Cwhile,
    'explicate_contol': typecheck_Ctup,
}


###################
# set interpreter #
###################

#interpLvar = interp_Lvar.InterpLvar().interp
#interpLif = interp_Lif.InterpLif().interp
#interpLwhile = interp_Lwhile.InterpLwhile().interp
interpLtup = interp_Ltup.InterpLtup().interp

#interpCif = interp_Cif.InterpCif().interp
interpCtup = interp_Ctup.InterpCtup().interp

interp_dict = {

    'shrink': interpLtup,

    'expose_allocation': interpLtup,

    #'remove_complex_operands': interpLvar,
    #'remove_complex_operands': interpLif,
    #'remove_complex_operands': interpLwhile,
    'remove_complex_operands': interpLtup,

    'explicate_control': interpCtup,  # bue 20241021: interp_Cwhile.py does not exist

    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}


#############
# run tests #
#############

if (args.tpathfile.lower() == 'all'):
    print('*** RUN ALL TESTS! ***')
    run_tests(
        lang = 'tup',
        compiler = compiler,
        compiler_name = 'tup',
        type_check_dict = typecheck_dict,
        interp_dict = interp_dict,
    )
else:
    print(f'*** RUN TEST {args.tpathfile}! ***')
    run_one_test(
        test = os.getcwd() + f'/{args.tpathfile}',
        lang = 'tup',
        compiler = compiler,
        compiler_name = 'tup',
        type_check_dict = typecheck_dict,
        interp_dict = interp_dict,
    )


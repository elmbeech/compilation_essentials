
    
typecheck_Ltup = type_check_Ltup.TypeCheckLtup().type_check
typecheck_Ctup = type_check_Ctup.TypeCheckCtup().type_check
typecheck_dict = {
    'source': typecheck_Ltup,
    'shrink': typecheck_Ltup,
    'expose_allocation': typecheck_Ltup,
    'remove_complex_operands': typecheck_Ltup,
    'explicate_control': typecheck_Ctup,
}
interpLtup = interp_Ltup.InterpLtup().interp
interpCtup = interp_Ctup.InterpCtup().interp
interp_dict = {
    'shrink': interpLtup,
    'expose_allocation': interpLtup,
    'remove_complex_operands': interpLtup,
    'explicate_control': interpCtup,
    #'select_instructions': racket_interp_pseudo_x86,
    #'assign_homes': racket_interp_x86,
    #'patch_instructions': racket_interp_x86,
}

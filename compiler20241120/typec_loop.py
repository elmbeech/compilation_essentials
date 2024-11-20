                
typecheck_Lwhile = type_check_Lwhile.TypeCheckLwhile().type_check
typecheck_Cwhile = type_check_Cwhile.TypeCheckCwhile().type_check
typecheck_dict = {
    'source': typecheck_Lwhile,
    'shrink': typecheck_Lwhile,
    'expose_allocation': typecheck_Lwhile,
    'remove_complex_operands': typecheck_Lwhile,
    'explicate_control': typecheck_Cwhile,
}
interpLwhile = interp_Lwhile.InterpLwhile().interp
interpCwhile = interp_Cif.InterpCif().interp
interp_dict = {
    'shrink': interpLwhile,
    'expose_allocation': interpLwhile,
    'remove_complex_operands': interpLwhile,
    'explicate_control': interpCwhile,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

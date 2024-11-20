            
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
            

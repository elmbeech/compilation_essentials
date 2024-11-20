
    ############################################################################
    # Patch Instructions
    ############################################################################

    def in_memory(self, a: arg) -> bool:
        if isinstance(a, Global):
            return True
        else:
            return super().in_memory(a)
    
    def patch_instructions(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                blocks = {l: self.patch_instrs(ss) for (l, ss) in body.items()}
                new_p = X86Program(blocks)
                new_p.stack_space = p.stack_space
                new_p.used_callee = p.used_callee
                new_p.num_root_spills = p.num_root_spills
                return new_p
            

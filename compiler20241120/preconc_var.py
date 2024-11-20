    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                prelude = [Instr('pushq', [Reg('rbp')]),
                           Instr('movq', [Reg('rsp'), Reg('rbp')]),
                           Instr('subq', [Immediate(p.stack_space),Reg('rsp')])]
                concl = [Instr('addq', [Immediate(p.stack_space),Reg('rsp')]),
                         Instr('popq', [Reg('rbp')]),
                         Instr('retq', [])]
                return X86Program(prelude + body + concl)


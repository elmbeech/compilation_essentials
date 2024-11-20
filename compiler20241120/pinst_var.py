    ############################################################################
    # Patch Instructions
    ############################################################################

    @staticmethod
    def big_constant(c: arg) -> bool:
        return (isinstance(c, Immediate) or isinstance(c, Constant)) \
            and (c.value > (2 ** 16) or c.value < - (2 ** 16))

    def in_memory(self, a: arg) -> bool:
        return isinstance(a, Deref)

    def patch_instr(self, i: instr) -> List[instr]:
        match i:
            case Instr('movq', [s, t]):
                if (self.in_memory(s) or self.big_constant(s)) \
                       and self.in_memory(t):
                    return [Instr('movq', [s, Reg('rax')]),
                            Instr('movq', [Reg('rax'), t])]
                else:
                    return [i]
            case Instr(inst, [s, t]) \
                if (self.in_memory(s) and self.in_memory(t)) \
                   or self.big_constant(s):
                return [Instr('movq', [s, Reg('rax')]),
                        Instr(inst, [Reg('rax'), t])]
            case _:
                return [i]

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        return sum([self.patch_instr(i) for i in ss], [])

    def patch_instructions(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                new_p = X86Program(self.patch_instrs(body))
                new_p.stack_space = p.stack_space
                return new_p


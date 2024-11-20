            
    ############################################################################
    # Prelude and Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                save_callee_reg = []
                for r in p.used_callee:
                    save_callee_reg.append(Instr('pushq', [Reg(r)]))
                restore_callee_reg = []
                for r in reversed(p.used_callee):
                    restore_callee_reg.append(Instr('popq', [Reg(r)]))
                rootstack_size = 2 ** 16
                #heap_size = 2 ** 16
                heap_size = 2 ** 4   # this size is good for revealing bugs
                initialize_heaps = \
                    [Instr('movq', [Immediate(rootstack_size), Reg('rdi')]), 
                     Instr('movq', [Immediate(heap_size), Reg('rsi')]),
                     Callq('initialize', 2),
                     Instr('movq', [Global('rootstack_begin'),
                                    Reg('r15')])]
                initialize_roots = []
                for i in range(0, p.num_root_spills):
                    initialize_roots += \
                        [Instr('movq', [Immediate(0), Deref('r15', 0)]),
                         Instr('addq', [Immediate(8), Reg('r15')])]
                main = [Instr('pushq', [Reg('rbp')]), \
                        Instr('movq', [Reg('rsp'), Reg('rbp')])] \
                        + save_callee_reg \
                        + [Instr('subq',[Immediate(p.stack_space),Reg('rsp')])]\
                        + initialize_heaps \
                        + initialize_roots \
                        + [Jump('start')]
                concl = [Instr('subq', [Immediate(8 * p.num_root_spills),
                                        Reg('r15')])] \
                      + [Instr('addq', [Immediate(p.stack_space),Reg('rsp')])] \
                      + restore_callee_reg \
                      + [Instr('popq', [Reg('rbp')]),
                         Instr('retq', [])]
                body['main'] = main
                body['conclusion'] = concl
                return X86Program(body)


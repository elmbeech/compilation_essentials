
    ###########################################################################
    # Uncover Live
    ###########################################################################

    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case Variable(id):
                return {a}
            case Reg(id):
                return {a}
            case Deref(reg, offset):     # don't need this case
                return {Reg(reg)}      # problem for write?
            case Immediate(value):
                return set()
            case _:
                raise Exception('error in vars_arg, unhandled: ' + repr(a))

    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr('movq', [s, t]):
                return self.vars_arg(s)
            case Instr(instr, args):
                return set().union(*[self.vars_arg(arg) for arg in args]) 
            case Callq(func, num_args): # what if num_args > len(arg_registers)??
                return set([Reg(r) for r in arg_registers[0:num_args]])
            case _:
                raise Exception('error in read_vars, unexpected: ' + repr(i))

    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr(instr, [t]):
                return self.vars_arg(t)
            case Instr('cmpq', [s1, s2]):
                return set()
            case Instr(instr, [s, t]):
                return self.vars_arg(t)
            case Callq(func, num_args):
                return set([Reg(r) for r in caller_save_for_alloc])
            case _:
                raise Exception('error in write_vars, unexpected: ' + repr(i))

    def uncover_live_instr(self, i: instr, live_before_succ: Set[location],
                           live_before: Dict[instr, Set[location]],
                           live_after: Dict[instr, Set[location]]):
        live_after[i] = live_before_succ
        live_before[i] = live_after[i].difference(self.write_vars(i)) \
                                      .union(self.read_vars(i))

    def trace_live(self, p: X86Program, live_before: Dict[instr, Set[location]],
                   live_after: Dict[instr, Set[location]]):
        match p:
          case X86Program(body):
            i = 0
            for s in body:
                if i == 0:
                    trace('\t' + str(live_before[s]))
                trace(str(s))
                trace('\t' + str(live_after[s]))
                i = i + 1
            trace("")
          
    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(body):
                live_before = {}
                live_after = {}
                live_before_succ = set([])
                for i in reversed(body):
                    self.uncover_live_instr(i, live_before_succ, live_before,
                                            live_after)
                    live_before_succ = live_before[i]

                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after


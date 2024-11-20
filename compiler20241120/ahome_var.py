    ############################################################################
    # Assign Homes
    ############################################################################

    def collect_locals_instr(self, i: instr) -> Set[location]:
        match i:
            case Instr(inst, args):
                lss = [self.collect_locals_arg(a) for a in args]
                return set().union(*lss)
            case Callq(func, num_args):
                return set()
            case _:
                raise Exception('error in collect_locals_instr, unknown: ' + repr(i))

    def collect_locals_arg(self, a: arg) -> Set[location]:
        match a:
            case Reg(id):
                return set()
            case Variable(id):
                return {Variable(id)}
            case Immediate(value):
                return set()
            case Deref(reg, offset):
                return set()
            case _:
                raise Exception('error in collect_locals_arg, unknown: ' + repr(a))

    def collect_locals_instrs(self, ss: List[stmt]) -> Set[location]:
        return set().union(*[self.collect_locals_instr(s) for s in ss])

    @staticmethod
    def gen_stack_access(i: int) -> arg:
        return Deref('rbp', -(8 + 8 * i))

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case Reg(id):
                return a
            case Variable(id):
                return home.get(a, a)
            case Immediate(value):
                return a
            case Deref(reg, offset):
                return Deref(reg, offset)
            case _:
                raise Exception('error in assign_homes_arg, unknown: ' + repr(a))

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        match i:
            case Instr(instr, args):
                new_args = [self.assign_homes_arg(a, home) for a in args]
                return Instr(instr, new_args)
            case Callq(func, num_args):
                return i
            case _:
                raise Exception('assign_homes_instr, unexpected: ' + repr(i))

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[Variable, arg]) -> List[instr]:
        return [self.assign_homes_instr(s, home) for s in ss]

    def assign_homes(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                variables = self.collect_locals_instrs(body)
                home = {}
                for i, x in enumerate(variables):
                    home[x] = self.gen_stack_access(i)
                body = self.assign_homes_instrs(body, home)
                p = X86Program(body)
                p.stack_space = align(8 * len(variables), 16)
                return p


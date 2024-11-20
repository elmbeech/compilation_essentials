
    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, a: expr) -> arg:
        match a:
            case Constant(True):
                return Immediate(1)
            case Constant(False):
                return Immediate(0)
            case Reg(id):  # cause how we handle Return
                return Reg(id)
            case _:
                return super().select_arg(a)

    def select_instructions(self, p: CProgram) -> X86Program:
        match p:
            case CProgram(body):
                blocks = {}
                for (l, ss) in body.items():
                    blocks[l] = sum([self.select_stmt(s) for s in ss], [])
                return X86Program(blocks)

    def select_stmt(self, s: stmt) -> List[instr]:
        match s:
            case If(Compare(left, [op], [right]), [Goto(thn)], [Goto(els)]):
                l = self.select_arg(left)
                r = self.select_arg(right)
                return [Instr('cmpq', [r, l]),
                        JumpIf(self.select_op(op), thn),
                        Jump(els)]
            case Goto(label):
                return [Jump(label)]
            case Assign([lhs], UnaryOp(Not(), operand)):
                new_lhs = self.select_arg(lhs)
                new_operand = self.select_arg(operand)
                return ([Instr('movq', [new_operand, new_lhs])]
                        if new_lhs != new_operand else []) \
                    + [Instr('xorq', [Immediate(1), new_lhs])]
            case Assign([lhs], BinOp(left, Sub(), right)) if left == lhs:
                new_lhs = self.select_arg(lhs)
                r = self.select_arg(right)
                return [Instr('subq', [r, new_lhs])]
            case Assign([lhs], Compare(left, [op], [right])):
                new_lhs = self.select_arg(lhs)
                l = self.select_arg(left)
                r = self.select_arg(right)
                # in cmpq, the left and right get swapped. -Jeremy
                if isinstance(r, Immediate):
                    comparison = [Instr('movq', [l, Reg('rax')]),
                                  Instr('cmpq', [r, Reg('rax')])]
                else:
                    comparison = [Instr('cmpq', [r, l])]
                return comparison + \
                       [Instr('set' + self.select_op(op), [ByteReg('al')]),
                        Instr('movzbq', [ByteReg('al'), new_lhs])]
            case Return(value):
                ins = self.select_stmt(Assign([Reg('rax')], value))
                return ins + [Jump('conclusion')]
            case _:
                return super().select_stmt(s)

    def select_op(self, op: operator) -> str:
        match op:
            case Sub():
                return 'subq'
            case And():
                return 'andq'
            case Eq():
                return 'e'
            case NotEq():
                return 'ne'
            case Lt():
                return 'l'
            case LtE():
                return 'le'
            case Gt():
                return 'g'
            case GtE():
                return 'ge'
            case _:
                return super().select_op(op)


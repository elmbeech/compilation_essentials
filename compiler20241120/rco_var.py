    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr, Temporaries]:
        match e:
            case Name(id):
                return e, []

            case Constant(value):
                if need_atomic and self.big_constant(e):
                    tmp = Name(generate_name('tmp'))
                    return tmp, [(tmp, Constant(value))]
                else:
                    return e, []

            case BinOp(left, op, right):
                (l, bs1) = self.rco_exp(left, True)
                (r, bs2) = self.rco_exp(right, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    b = BinOp(l, op, r)
                    return tmp, bs1 + bs2 + [(tmp, b)]
                else:
                    return BinOp(l, op, r), bs1 + bs2

            # needed for tests/int64/min-int.py
            case UnaryOp(USub(), Constant(value)):
              return self.rco_exp(Constant(-value), need_atomic)

            case UnaryOp(op, operand):
                (rand, bs) = self.rco_exp(operand, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, bs + [(tmp, UnaryOp(op, rand))]
                else:
                    return UnaryOp(op, rand), bs

            case Call(func, args):
                (new_func, bs1) = self.rco_exp(func, True)
                (new_args, bss2) = \
                    unzip([self.rco_exp(arg, True) for arg in args])
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return (tmp, bs1 + sum(bss2, [])
                            + [(tmp, Call(new_func, new_args, []))])
                else:
                    return Call(new_func, new_args, []), bs1 + sum(bss2, [])
            case _:
                raise Exception('error in rco_exp, unhandled: ' + repr(e))

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Assign(targets, value):
                new_value, bs = self.rco_exp(value, False)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] \
                    + [Assign(targets, new_value)]
            case Expr(value):
                new_value, bs = self.rco_exp(value, False)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] \
                    + [Expr(new_value)]
            case _:
                raise Exception('error in rco_stmt, unhandled: ' + repr(s))

    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(body):
                sss = [self.rco_stmt(s) for s in body]
                return Module(sum(sss, []))
            case _:
                raise Exception('error remove_complex_operators, unhandled: '\
                                + repr(p))


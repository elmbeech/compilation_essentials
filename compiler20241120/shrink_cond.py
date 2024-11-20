    ############################################################################
    # Shrink
    ############################################################################

    def shrink(self, p: Module) -> Module:
        match p:
            case Module(body):
                return Module([self.shrink_stmt(s) for s in body])

    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case Assign(targets, value):
                return Assign([self.shrink_exp(e) for e in targets],
                              self.shrink_exp(value))
            case Expr(value):
                return Expr(self.shrink_exp(value))
            case If(test, body, orelse):
                return If(self.shrink_exp(test),
                          [self.shrink_stmt(s) for s in body],
                          [self.shrink_stmt(s) for s in orelse])
            case _:
                raise Exception('shrink_stmt: unexpected: ' + repr(s))

    def shrink_exp(self, e: expr) -> expr:
        match e:
            case Name(id):
                return e
            case Constant(value):
                return e
            case BinOp(left, op, right):
                l = self.shrink_exp(left);
                r = self.shrink_exp(right)
                return BinOp(l, op, r)
            case UnaryOp(op, operand):
                rand = self.shrink_exp(operand)
                return UnaryOp(op, rand)
            case Call(func, args):
                fun = self.shrink_exp(func)
                new_args = [self.shrink_exp(arg) for arg in args]
                return Call(fun, new_args)
            case IfExp(test, body, orelse):
                tst = self.shrink_exp(test)
                bod = self.shrink_exp(body);
                els = self.shrink_exp(orelse)
                return IfExp(tst, bod, els)
            # Replace And with IfExp
            case BoolOp(And(), values):  # values was [left,right], bug? -Jeremy
                l = self.shrink_exp(values[0])
                r = self.shrink_exp(values[1])
                return IfExp(l, r, Constant(False))
            # Replace Or with IfExp
            case BoolOp(Or(), values):
                l = self.shrink_exp(values[0])
                r = self.shrink_exp(values[1])
                return IfExp(l, Constant(True), r)
            case Compare(left, [op], [right]):
                l = self.shrink_exp(left);
                r = self.shrink_exp(right)
                return Compare(l, [op], [r])
            case _:
                raise Exception('shrink_exp: ' + repr(e))


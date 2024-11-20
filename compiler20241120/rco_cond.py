
    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case If(test, body, orelse):
                (test, bs) = self.rco_exp(test, False)
                sss1 = [self.rco_stmt(s) for s in body]
                sss2 = [self.rco_stmt(s) for s in orelse]
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] \
                       + [If(test, sum(sss1, []), sum(sss2, []))]
            case _:
                return super().rco_stmt(s)

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr,Temporaries]:
        match e:
            case IfExp(test, body, orelse):
                (new_test, bs1) = self.rco_exp(test, False)
                (new_body, bs2) = self.rco_exp(body, False)
                (new_orelse, bs3) = self.rco_exp(orelse, False)
                new_body = make_begin(bs2, new_body)
                new_orelse = make_begin(bs3, new_orelse)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return (tmp, bs1 + [(tmp, IfExp(new_test, new_body,
                                                    new_orelse))])
                else:
                    return IfExp(new_test, new_body, new_orelse), bs1
            case Compare(left, [op], [right]):
                (l, bs1) = self.rco_exp(left, True)
                (r, bs2) = self.rco_exp(right, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, bs1 + bs2 + [(tmp, Compare(l, [op], [r]))]
                else:
                    return Compare(l, [op], [r]), bs1 + bs2
            case _:
                return super().rco_exp(e, need_atomic)


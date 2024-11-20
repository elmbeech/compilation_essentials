
    ############################################################################
    # Remove Complex Operands
    ############################################################################
    
    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case While(test, body, []):
                (test, bs) = self.rco_exp(test, False)
                sss1 = [self.rco_stmt(s) for s in body]
                return [While(make_begin(bs, test), sum(sss1, []), [])]
            case _:
                return super().rco_stmt(s)
    

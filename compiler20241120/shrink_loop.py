    
    ############################################################################
    # Shrink
    ############################################################################
    
    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case While(test, body, []):
                return While(self.shrink_exp(test),
                             [self.shrink_stmt(s) for s in body],
                             [])
            case _:
                return super().shrink_stmt(s)


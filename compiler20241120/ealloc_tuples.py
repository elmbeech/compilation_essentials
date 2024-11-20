
    ###########################################################################
    # Expose Allocation
    ###########################################################################

    def expose_allocation(self, p: Module) -> Module:
      match p:
        case Module(body):
          return Module([self.expose_alloc_stmt(s) for s in body])

    def expose_alloc_stmt(self, s: stmt) -> stmt:
        match s:
            case Assign(targets, value):
                return Assign(targets, self.expose_alloc_exp(value))
            case Expr(value):
                return Expr(self.expose_alloc_exp(value))
            case If(test, body, orelse):
                return If(self.expose_alloc_exp(test),
                          [self.expose_alloc_stmt(s) for s in body],
                          [self.expose_alloc_stmt(s) for s in orelse])
            case While(test, body, []):
                return While(self.expose_alloc_exp(test),
                             [self.expose_alloc_stmt(s) for s in body], [])
            case _:
                raise Exception('expose_alloc_stmt: unexpected ' + repr(s))

    def expose_alloc_tuple(self, es, tupleType, allocExp):
        n = len(es)
        size = (n + 1) * 8
        vec = generate_name('alloc')
        freeptr_size = BinOp(GlobalValue('free_ptr'), Add(), Constant(size))
        space_left = Compare(freeptr_size, [Lt()],
                             [GlobalValue('fromspace_end')])
        xs = [Name(generate_name('init')) for e in es]
        inits = [Assign([x], e) for (x,e) in zip(xs,es)]
        initVec = []
        i = 0
        for x in xs:
            initVec += [Assign([Subscript(Name(vec), Constant(i),Store())], x)]
            i += 1
        return Begin(inits \
                     + [If(space_left, [], [Collect(size)])] \
                     + [Assign([Name(vec)], allocExp)] \
                     + initVec,
                     Name(vec))

    def expose_alloc_exp(self, e: expr) -> expr:
        match e:
            case Name(id):
                return e
            case Constant(value):
                return e
            case BinOp(left, op, right):
                l = self.expose_alloc_exp(left)
                r = self.expose_alloc_exp(right)
                return BinOp(l, op, r)
            case UnaryOp(op, operand):
                rand = self.expose_alloc_exp(operand)
                return UnaryOp(op, rand)
            case Call(func, args):
                fun = self.expose_alloc_exp(func)
                new_args = [self.expose_alloc_exp(arg) for arg in args]
                return Call(fun, new_args)
            case IfExp(test, body, orelse):
                tst = self.expose_alloc_exp(test)
                bod = self.expose_alloc_exp(body)
                els = self.expose_alloc_exp(orelse)
                return IfExp(tst, bod, els)
            case Begin(body, result):
                new_body = [self.expose_alloc_stmt(s) for s in body]
                new_result = self.expose_alloc_exp(result)
                return Begin(new_body, new_result)
            case Compare(left, [op], [right]):
                l = self.expose_alloc_exp(left);
                r = self.expose_alloc_exp(right)
                return Compare(l, [op], [r])
            case Tuple(es, Load()):
                new_es = [self.expose_alloc_exp(e) for e in es]
                alloc = Allocate(len(new_es), e.has_type)
                return self.expose_alloc_tuple(new_es, e.has_type, alloc)
            case Subscript(tup, index, Load()):
                return Subscript(self.expose_alloc_exp(tup),
                                 self.expose_alloc_exp(index),
                                 Load())
            case _:
                raise Exception('expose_alloc_exp: unexpected ' + repr(e))


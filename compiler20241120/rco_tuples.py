
    ###########################################################################
    # Remove Complex Operands
    ###########################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr,Temporaries]:
      match e:
        # Begin handled here because previous pass now adds Begin
        case Begin(body, result):
          sss = [self.rco_stmt(s) for s in body]
          (new_result, bs) = self.rco_exp(result, False)
          ss = make_assigns(bs)
          new_e = Begin(sum(sss, []) + ss, new_result)
          if need_atomic:
            tmp = Name(generate_name('tmp'))
            return (tmp, [(tmp, new_e)])
          else:
            return (new_e, [])
        case GlobalValue(name):
          return (e, [])      
        case Allocate(length, ty):
          if need_atomic:
            tmp = Name(generate_name('tmp'))
            return (tmp, [(tmp, e)])
          else:
            return (e, [])
        case Subscript(tup, index, Load()):
          (new_tup, bs1) = self.rco_exp(tup, True)
          (new_index, bs2) = self.rco_exp(index, True)
          new_e = Subscript(new_tup, new_index, Load())
          if need_atomic:
              tmp = Name(generate_name('tmp'))
              return (tmp, bs1 + bs2 + [(tmp, new_e)])
          else:
              return (new_e, bs1 + bs2)
        case _:
          return super().rco_exp(e, need_atomic)

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Assign([Subscript(tup, index, Store())], value):
                new_tup, bs1 = self.rco_exp(tup, True)
                new_value, bs2 = self.rco_exp(value, True)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs1] \
                    + [Assign([lhs], rhs) for (lhs, rhs) in bs2] \
                    + [Assign([Subscript(new_tup, index, Store())], new_value)]
            case Collect(amount):
                return [Collect(amount)]
            case _:
                return super().rco_stmt(s)
      

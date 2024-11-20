
    ###########################################################################
    # Shrink
    ###########################################################################

    def shrink_exp(self, e: expr) -> expr:
      match e:
        case Tuple(es, Load()):
          new_es = [self.shrink_exp(e) for e in es]
          return Tuple(new_es, Load())
        case Subscript(tup, index, Load()):
          return Subscript(self.shrink_exp(tup), self.shrink_exp(index), Load())
        case _:
          return super().shrink_exp(e)


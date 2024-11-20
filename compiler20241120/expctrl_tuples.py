      
  ############################################################################
  # Explicate Control
  ############################################################################

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Subscript(tup, index, Load()):
                tmp = generate_name('tmp')
                assn = [Assign([Name(tmp)], cnd)]
                return assn + self.generic_explicate_pred(Name(tmp), thn, els,
                                                          basic_blocks)
            case _:
                return super().explicate_pred(cnd, thn, els, basic_blocks)
            
    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Collect(amount):
                return [Collect(amount)] + cont
            case _:
                return super().explicate_stmt(s, cont, basic_blocks)
          

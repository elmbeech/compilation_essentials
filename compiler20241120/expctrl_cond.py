
    ############################################################################
    # Explicate Control
    ############################################################################

    def create_block(self, stmts: List[stmt],
                     basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match stmts:
          case [Goto(l)]:
            return stmts
          case _:
            label = generate_name('block')
            basic_blocks[label] = stmts
            return [Goto(label)]

    def explicate_effect(self, e: expr, cont: List[stmt],
                         basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Begin(body, result):
                ss = self.explicate_effect(result, cont, basic_blocks)
                for s in reversed(body):
                  ss = self.explicate_stmt(s, ss, basic_blocks)
                return ss
            case IfExp(test, body, orelse):
                goto = self.create_block(cont, basic_blocks)
                new_body = self.explicate_effect(body, goto, basic_blocks)
                new_orelse = self.explicate_effect(orelse, goto, basic_blocks)
                return self.explicate_pred(test, new_body, new_orelse,
                                           basic_blocks)
            case Call(func, args):
                return [Expr(e)] + cont
            case _:  # no effect, remove this expression
                return cont

    def explicate_assign(self, e: expr, x: Variable, cont: List[stmt],
                         basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Begin(body, result):
              ss = self.explicate_assign(result, x, cont, basic_blocks)
              for s in reversed(body):
                  ss = self.explicate_stmt(s, ss, basic_blocks)
              return ss
            case IfExp(test, body, orelse):
                goto = self.create_block(cont, basic_blocks)
                new_body = self.explicate_assign(body, x, goto, basic_blocks)
                new_orelse = self.explicate_assign(orelse, x, goto,
                                                   basic_blocks)
                return self.explicate_pred(test, new_body, new_orelse,
                                           basic_blocks)
            case _:
                return [Assign([x], e)] + cont
            
    def generic_explicate_pred(self, cnd: expr, thn: List[stmt],
                               els: List[stmt],
                               basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        return [If(Compare(cnd, [Eq()], [Constant(False)]),
                   self.create_block(els, basic_blocks),
                   self.create_block(thn, basic_blocks))]

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Name(x):
                return self.generic_explicate_pred(cnd, thn, els, basic_blocks)
            case Compare(left, [op], [right]):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                return [If(cnd, goto_thn, goto_els)]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case UnaryOp(Not(), operand):
                return self.explicate_pred(operand, els, thn, basic_blocks)
            case Begin(body, result):
              ss = self.explicate_pred(result, thn, els, basic_blocks)
              for s in reversed(body):
                  ss = self.explicate_stmt(s, ss, basic_blocks)
              return ss
            case IfExp(test, body, orelse):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                new_body = self.explicate_pred(body, goto_thn, goto_els,
                                               basic_blocks)
                new_els = self.explicate_pred(orelse, goto_thn, goto_els,
                                              basic_blocks)
                return self.explicate_pred(test, new_body, new_els,
                                           basic_blocks)
            case _:
                raise Exception('explicate_pred: unexpected ' + repr(cnd))

    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                goto = self.create_block(cont, basic_blocks)
                new_body = goto
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                new_els = goto
                for s in reversed(orelse):
                    new_els = self.explicate_stmt(s, new_els, basic_blocks)
                return self.explicate_pred(test, new_body, new_els,
                                           basic_blocks)
            case _:
                raise Exception('explicate_stmt: unexpected ' + repr(s))

    def explicate_control(self, p: Module) -> CProgram:
        match p:
            case Module(body):
                new_body = [Return(Constant(0))]
                basic_blocks = {}
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                basic_blocks['start'] = new_body
                return CProgram(basic_blocks)
            case _:
                raise Exception('explicate_control: unexpected ' + repr(p))


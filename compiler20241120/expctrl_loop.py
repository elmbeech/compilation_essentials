    
    ############################################################################
    # Explicate Control
    ############################################################################
    
    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case While(test, body, []):
                label = generate_name('loop')
                new_body = [Goto(label)]
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, blocks)
                loop = self.explicate_pred(test, new_body, cont, blocks)
                blocks[label] = loop
                return [Goto(label)]
            case _:
                return super().explicate_stmt(s, cont, blocks)


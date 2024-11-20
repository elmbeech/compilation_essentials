
    ############################################################################
    # Uncover Live
    ############################################################################

    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case ByteReg(id):
                return {Reg(byte_to_full_reg[id])}
            case _:
                return super().vars_arg(a)

    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Jump(label):
                return set()
            case JumpIf(cc, label):
                return set()
            case _:
                return super().read_vars(i)

    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case Jump(label):
                return set()
            case JumpIf(cc, label):
                return set()
            case Instr('cmpq', args):
                return {Reg('__flag')}
            case _:
                return super().write_vars(i)

    @staticmethod
    def adjacent_instr(s: instr) -> List[str]:
        if isinstance(s, Jump) or isinstance(s, JumpIf):
            return [s.label]
        else:
            return []

    def blocks_to_graph(self,
                        blocks: Dict[str, List[instr]]) -> DirectedAdjList:
        graph = DirectedAdjList()
        for u in blocks.keys():
            graph.add_vertex(u)
        for (u, ss) in blocks.items():
            for s in ss:
                for v in self.adjacent_instr(s):
                    graph.add_edge(u, v)
        return graph

    def trace_live_blocks(self, blocks, live_before: Dict[instr, Set[location]],
                   live_after: Dict[instr, Set[location]]):
        for (l, ss) in blocks.items():
            trace(l + ':\n')
            i = 0 
            for s in ss:
                if i == 0:
                    trace('\t\t{' + ', '.join([str(l) for l in live_before[s]]) + '}')
                trace(str(s))
                trace('\t\t{' + ', '.join([str(l) for l in live_after[s]]) + '}')
                i = i + 1
                
    def trace_live(self, p: X86Program, live_before: Dict[instr, Set[location]],
                   live_after: Dict[instr, Set[location]]):
        match p:
            case X86Program(body):
                self.trace_live_blocks(body, live_before, live_after)
                
    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(body):
                live_before = {}
                live_after = {}
                cfg = self.blocks_to_graph(body)
                cfg_trans = transpose(cfg)
                live_before_block = \
                    {'conclusion': {Reg('rax'), Reg('rsp')}}
                for l in topological_sort(cfg_trans):
                    if l != 'conclusion':
                        adj_live = [live_before_block[v] \
                                    for v in cfg.adjacent(l)]
                        live_before_succ = set().union(*adj_live)
                        for i in reversed(body[l]):
                            self.uncover_live_instr(i, live_before_succ,
                                                    live_before, live_after)
                            live_before_succ = live_before[i]
                        live_before_block[l] = live_before_succ
                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after



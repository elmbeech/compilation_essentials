

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference_blocks(self, blocks,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        graph = UndirectedAdjList()
        for (l, ss) in blocks.items():
            for i in ss:
                self.interfere_instr(i, graph, live_after)
        return graph
        
    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(blocks):
                return self.build_interference_blocks(blocks, live_after)

    def interfere_instr(self, i: instr, graph,
                        live_after: Dict[instr, Set[location]]):
        match i:
            case Instr('movzbq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)
            case _:
                return super().interfere_instr(i, graph, live_after)


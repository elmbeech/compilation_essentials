
    ###########################################################################
    # Build Interference
    ###########################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(body):
                G = UndirectedAdjList()
                for i in body:
                    self.interfere_instr(i, G, live_after)
                return G

    def interfere_instr(self, i: instr, graph: UndirectedAdjList,
                        live_after: Dict[instr, Set[location]]):
        match i:
            case Instr('movq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)
            case _:
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d:
                            graph.add_edge(d, v)


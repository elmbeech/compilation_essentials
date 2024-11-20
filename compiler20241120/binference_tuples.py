
    ###########################################################################
    # Build Interference
    ###########################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(body):
                self.var_types = p.var_types
                return super().build_interference(p, live_after)

    def interfere_instr(self, i: instr, graph: UndirectedAdjList,
                        live_after: Dict[instr, Set[location]]):
        match i:
            case Callq(func, n) if func == 'collect':
                for v in live_after[i]:
                    if not (v.id in registers) and self.is_root_type(self.var_types[v.id]):
                        for u in callee_save_for_alloc:
                            graph.add_edge(Reg(u), v)
                super().interfere_instr(i, graph, live_after)
            case _:
                super().interfere_instr(i, graph, live_after)
                            


    ###########################################################################
    # Allocate Registers
    ###########################################################################

    def choose_color(self, v, unavail_colors):
        i = 0
        while i in unavail_colors[v]:
            i += 1
        return i
    
    # O(n * n * log(n))
    def color_graph(self, graph: UndirectedAdjList,
                    variables: Set[location]) -> Tuple[Dict[location, int], Set[location]]:
        spills = set()
        unavail_colors = {}
        def compare(u, v):
            return len(unavail_colors[u.key]) < len(unavail_colors[v.key])
        Q = PriorityQueue(compare)
        color = {}
        for r in registers_for_alloc:
            color[Reg(r)] = register_color[r]
        for x in variables: # O(n log n), no its O(n * n)
            adj_reg = [y for y in graph.adjacent(x) if y.id in registers]
            unavail_colors[x] = \
                set().union([register_color[r.id] for r in adj_reg])
            Q.push(x) # O(log n)
        while not Q.empty():  # n iterations
            v = Q.pop() # O(log n)
            c = self.choose_color(v, unavail_colors)
            color[v] = c
            if c >= len(registers_for_alloc):
                spills = spills.union(set([v]))  # add method instead?
            for u in graph.adjacent(v): # n iterations
                if u.id not in registers: # use match on u instead?
                    unavail_colors[u].add(c)
                    Q.increase_key(u)  # log(n)
        return color, spills

    def identify_home(self, c: int, first_location: int) -> arg:
        if c < len(registers_for_alloc):
            return Reg(registers_for_alloc[c])
        else:
            offset = first_location + 8 * (c - len(registers_for_alloc))
            return Deref('rbp', - offset)

    def is_callee_color(self, c: int) -> bool:
        return c < len(registers_for_alloc) \
            and registers_for_alloc[c] in callee_save

    def used_callee_reg(self, variables: Set[location],
                        color: Dict[location, int]) -> Set[str]:
        result = set()
        for x in variables:
            if self.is_callee_color(color[x]):
                result.add(registers_for_alloc[color[x]])
        return list(result)

    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86Program(body):
                variables = self.collect_locals_instrs(body)
                (color, spills) = self.color_graph(graph, variables)
                trace("color")
                trace(color)
                trace("")
                used_callee = self.used_callee_reg(variables, color)
                num_callee = len(used_callee)
                home = {}
                for x in variables:
                    home[x] = self.identify_home(color[x], 8 + 8 * num_callee)
                trace("home")
                trace(home)
                trace("")
                new_body = [self.assign_homes_instr(s, home) for s in body]
                new_p = X86Program(new_body)
                new_p.stack_space = align(8 * (num_callee + len(spills)), 16) \
                    - 8 * num_callee
                new_p.used_callee = used_callee
                return new_p

    def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
        live_after = self.uncover_live(pseudo_x86)
        graph = self.build_interference(pseudo_x86, live_after)
        #trace(graph.show().source)
        trace("")
        return self.allocate_registers(pseudo_x86, graph)
            

                            
    ###########################################################################
    # Allocate Registers
    ###########################################################################

    def valid_color(self, c, v, unavail_colors):
        return (not (c in unavail_colors[v])) \
            and ((c < len(registers_for_alloc)) \
                 or (self.is_root_type(self.var_types[v.id]) and c%2 == 0) \
                 or (not self.is_root_type(self.var_types[v.id]) and c%2 == 1))
    
    def choose_color(self, v, unavail_colors):
        c = 0
        while not self.valid_color(c, v, unavail_colors):
            c += 1
        return c

    def identify_home(self, c: int, first_location: int) -> arg:
        n = len(registers_for_alloc)
        if c < n:
            return Reg(registers_for_alloc[c])
        elif c%2 == 0: # root stack
            new_c = floor((c - n) / 2)
            offset = - 8*(new_c + 1)
            return Deref('r15', offset)
        else:          # regular stack
            new_c = floor((c - n) / 2)
            trace("color: " + repr(c) + ", new color: " + repr(new_c) + "\n")
            offset = - (first_location + 8 * new_c)
            return Deref('rbp', offset)

    def alloc_reg_blocks(self, blocks,
                         graph: UndirectedAdjList,
                         var_types) -> X86Program:
        variables = set().union(*[self.collect_locals_instrs(ss) \
                                  for (l, ss) in blocks.items()])
        self.var_types = var_types
        trace('var_types:')
        trace(var_types)
        (color, spills) = self.color_graph(graph, variables)
        # trace('spills:')
        # trace(spills)
        # trace('color:')
        # trace(color)
        root_spills = set()
        stack_spills = set()
        for s in spills:
            if self.is_root_type(var_types[s.id]):
                root_spills = root_spills.union(set([s.id]))
            else:
                stack_spills = stack_spills.union(set([s.id]))
        used_callee = self.used_callee_reg(variables, color)
        num_callee = len(used_callee)
        home = {x: self.identify_home(color[x], 8 + 8 * num_callee) \
                for x in variables}
        trace('home:')
        trace(home)
        new_blocks = {l: self.assign_homes_instrs(ss, home) \
               for (l, ss) in blocks.items()}
        return (new_blocks, used_callee, num_callee, stack_spills, root_spills)
        
    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86Program(blocks):
                (new_blocks, used_callee, num_callee, stack_spills, root_spills) = \
                    self.alloc_reg_blocks(blocks, graph, p.var_types)
                new_p = X86Program(new_blocks)
                new_p.stack_space = \
                    align(8 * (num_callee + len(stack_spills)), 16) \
                    - 8 * num_callee
                new_p.used_callee = used_callee
                new_p.num_root_spills = len(root_spills)
                return new_p
            

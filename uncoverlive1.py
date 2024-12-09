
    def vars_arg(self,
            a: arg
        ) -> Set[location]:
        match a:
            case Variable(id):
                return {a}

            case Reg(id):
                return {a}

            case Deref(reg, offset):     # don't need this case
                return {Reg(reg)}      # problem for write?

            case Immediate(value):
                return set()

            case ByteReg(id):
                return {Reg(byte_to_full_reg[id])}

            case _:
                raise Exception('error in vars_arg, unhandled: ' + repr(a))


    def read_vars(self,
            i: instr
        ) -> Set[location]:
        match i:
            case Instr('movq', [s, t]):
                return self.vars_arg(s)

            case Instr(instr, args):
                return set().union(*[self.vars_arg(arg) for arg in args])

            case Callq(func, num_args): # what if num_args > len(arg_registers)??
                return set([Reg(r) for r in arg_registers[0:num_args]])

            case Jump(label):
                return set()

            case JumpIf(cc, label):
                return set()

            case _:
                raise Exception('error in read_vars, unexpected: ' + repr(i))


    def write_vars(self,
            i: instr
        ) -> Set[location]:
        match i:
            case Instr(instr, [t]):
                return self.vars_arg(t)

            case Instr('cmpq', [s1, s2]):
                return set()

            case Instr(instr, [s, t]):
                return self.vars_arg(t)

            case Callq(func, num_args):
                return set([Reg(r) for r in caller_save_for_alloc])

            case Jump(label):
                return set()

            case JumpIf(cc, label):
                return set()

            case Instr('cmpq', args):
                return {Reg('__flag')}

            case _:
                raise Exception('error in write_vars, unexpected: ' + repr(i))


    def uncover_live_instr(self,
            i : instr,
            live_before_succ : Set[location],
            live_before : Dict[instr, Set[location]],
            live_after : Dict[instr, Set[location]]
        ):
        live_after[i] = live_before_succ
        live_before[i] = live_after[i].difference(self.write_vars(i)).union(self.read_vars(i))


    def uncover_live_block(self,
            label : str,
            ss : List[stmt],
            live : Set[location],
            live_before : Dict[instr, Set[location]],
            live_after : Dict[instr, Set[location]]
        ) -> Set[location]:
        for i in reversed(ss):
            self.uncover_live_instr(i, live, live_before, live_after)
            live = live_before[i]
        return live


    # This is a method so it can be overridden (e.g. in functions.py)
    def liveness_transfer(self,
            blocks : Dict[str, List[instr]],
            cfg : DirectedAdjList,
            live_before : Dict[instr, Set[location]],
            live_after : Dict[instr, Set[location]]
        ) -> Set[location]:
        def live_xfer(label, live_before_succ):
            if label == 'conclusion':
                return {Reg('rax'), Reg('rsp')}
            else:
                return self.uncover_live_block(label, blocks[label], live_before_succ, live_before, live_after)
        return live_xfer


####
    # bue why not self?
    @staticmethod
    def adjacent_instr(s: instr) -> List[str]:
        if isinstance(s, Jump) or isinstance(s, JumpIf):
            return [s.label]
        else:
            return []


    def blocks_to_graph(self,
            blocks : Dict[str, List[instr]]
        ) -> DirectedAdjList:
        graph = DirectedAdjList()
        for u in blocks.keys():
            graph.add_vertex(u)
        for (u, ss) in blocks.items():
            for s in ss:
                for v in self.adjacent_instr(s):
                    graph.add_edge(u, v)
        return graph


    def uncover_live_blocks(self,
            blocks : Dict[str, List[instr]]
        ):
        live_before = {}
        live_after = {}
        cfg = self.blocks_to_graph(blocks)
        transfer = self.liveness_transfer(blocks, cfg, live_before, live_after)
        bottom = set()
        join = lambda s, t: s.union(t)
        # liveness is a backward analysis, so we transpose the CFG
        analyze_dataflow(transpose(cfg), transfer, bottom, join)
        return live_before, live_after


####
    def trace_live_blocks(self,
            blocks : Dict[str, List[instr]],
            live_before : Dict[instr, Set[location]],
            live_after : Dict[instr, Set[location]]
        ):
        for (l, ss) in blocks.items():
            trace(l + ':\n')
            i = 0
            for s in ss:
                if i == 0:
                    trace('\t\t{' + ', '.join([str(l) for l in live_before[s]]) + '}')
                trace(str(s))
                trace('\t\t{' + ', '.join([str(l) for l in live_after[s]]) + '}')
                i = i + 1


    def trace_live(self,
            p : X86Program,
            live_before : Dict[instr, Set[location]],
            live_after : Dict[instr, Set[location]]
        ):
        match p:
            case X86Program(body):
                self.trace_live_blocks(body, live_before, live_after)


####

    def live_interval(self,
        p : X86Program,
        ) -> Dict[location : int]:
        d_liveinterval = {}

           

####
    def uncover_live(self,
            p : X86Program
        ) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(blocks):
                (live_before, live_after) = self.uncover_live_blocks(blocks)
                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after


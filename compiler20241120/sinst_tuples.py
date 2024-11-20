          
    ###########################################################################
    # Select Instructions
    ###########################################################################

    def select_op(self, op: operator) -> str:
      match op:
        case Is():
          return 'e'
        case _:
          return super().select_op(op)
          
    def is_root_type(self, t):
      match t:
        case TupleType(ts):
          return True
        case _:
          return False

    def select_arg(self, a: expr) -> arg:
      match a:
        case GlobalValue(name):
          return Global(name)
        case _:
          return super().select_arg(a)
      
    def select_stmt(self, s: stmt) -> List[instr]:
      match s:
        case Assign([lhs], Allocate(length, TupleType(ts))):
            new_lhs = self.select_arg(lhs)
            size = 8 * (length + 1)
            is_not_fwd_tag = 1
            length_tag = length << 1
            ptr_tag = 0
            i = 7
            for t in ts:
                ptr_tag |= bool2int(self.is_root_type(t)) << i
                i = i + 1
            tag = ptr_tag | length_tag | is_not_fwd_tag
            return [Instr('movq', [Global('free_ptr'),
                                   Reg('r11')]),
                    Instr('addq', [Immediate(size),
                                   Global('free_ptr')]),
                    Instr('movq', [Immediate(tag), Deref('r11', 0)]),
                    Instr('movq', [Reg('r11'), new_lhs])]
        case Collect(size):
            return [Instr('movq', [Reg('r15'), Reg('rdi')]),
                    Instr('movq', [self.select_arg(Constant(size)),
                                   Reg('rsi')]),
                    Callq('collect', 2)]
        case Assign([lhs], Subscript(tup, index, Load())):
            new_lhs = self.select_arg(lhs)
            new_tup = self.select_arg(tup)
            new_index = self.select_arg(index).value
            return [Instr('movq', [new_tup, Reg('r11')]),
                    Instr('movq', [Deref('r11', 8 * (new_index + 1)), new_lhs])]
        case Assign([Subscript(tup, index, Store())], rhs):
            new_tup = self.select_arg(tup)
            new_index = self.select_arg(index).value
            new_rhs = self.select_arg(rhs)
            return [Instr('movq', [new_tup, Reg('r11')]),
                    Instr('movq', [new_rhs, Deref('r11', 8*(new_index + 1))])]
        case Assign([lhs], Call(Name('len'), [tup])):
            new_lhs = self.select_arg(lhs)        
            new_tup = self.select_arg(tup)
            return [Instr('movq', [new_tup, Reg('rax')]),
                    Instr('movq', [Deref('rax', 0), Reg('rax')]),
                    Instr('andq', [Immediate(126), Reg('rax')]),
                    Instr('sarq', [Immediate(1), Reg('rax')]),
                    Instr('movq', [Reg('rax'), new_lhs])]
        case _:
            return super().select_stmt(s)

    def select_instructions(self, p: CProgram) -> X86Program:
        match p:
            case CProgram(body):
                blocks = {}
                for (l, ss) in body.items():
                    blocks[l] = sum([self.select_stmt(s) for s in ss], [])
                new_p = X86Program(blocks)
                new_p.var_types = p.var_types
                return new_p
  

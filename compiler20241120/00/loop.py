# Language L_While

# Concrete Syntax

# stmt ::= ... | `while` exp `:` stmt+

# Abstract Syntax

#  stmt ::= ... | While(exp, stmt+, [])

from ast import *
from utils import *
from x86_ast import *
import cond
from dataflow_analysis import analyze_dataflow
from typing import List, Dict, Set
from graph import DirectedAdjList, transpose
import type_check_Lwhile
import interp_Lwhile
import interp_Cif
import type_check_Cwhile
from eval_x86 import interp_x86

class WhileLoops(cond.Conditionals):
    
    ############################################################################
    # Shrink
    ############################################################################
    
    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case While(test, body, []):
                return While(self.shrink_exp(test),
                             [self.shrink_stmt(s) for s in body],
                             [])
            case _:
                return super().shrink_stmt(s)

    ############################################################################
    # Remove Complex Operands
    ############################################################################
    
    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case While(test, body, []):
                (test, bs) = self.rco_exp(test, False)
                sss1 = [self.rco_stmt(s) for s in body]
                return [While(make_begin(bs, test), sum(sss1, []), [])]
            case _:
                return super().rco_stmt(s)
    
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

    ############################################################################
    # Uncover Live
    ############################################################################

    def uncover_live_block(self, label : str,
                           ss : List[stmt],
                           live : Set[location],
                           live_before : Dict[instr, Set[location]],
                           live_after : Dict[instr, Set[location]]) -> Set[location]:
        for i in reversed(ss):
            self.uncover_live_instr(i, live, live_before, live_after)
            live = live_before[i]
        return live

    # This is a method so it can be overridden (e.g. in functions.py)
    def liveness_transfer(self, blocks : Dict[str, List[instr]],
                          cfg : DirectedAdjList,
                          live_before : Dict[instr, Set[location]],
                          live_after : Dict[instr, Set[location]]) -> Set[location]:
        def live_xfer(label, live_before_succ):
            if label == 'conclusion':
                return {Reg('rax'), Reg('rsp')}
            else:
                return self.uncover_live_block(label, blocks[label], live_before_succ,
                                               live_before, live_after)
        return live_xfer

    def uncover_live_blocks(self, blocks):
        live_before = {}
        live_after = {}
        cfg = self.blocks_to_graph(blocks)
        transfer = self.liveness_transfer(blocks, cfg, live_before, live_after)
        bottom = set()
        join = lambda s, t: s.union(t)
        # liveness is a backward analysis, so we transpose the CFG
        analyze_dataflow(transpose(cfg), transfer, bottom, join)
        return live_before, live_after
    
    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(blocks):
                (live_before, live_after) = self.uncover_live_blocks(blocks)
                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after
                
typecheck_Lwhile = type_check_Lwhile.TypeCheckLwhile().type_check
typecheck_Cwhile = type_check_Cwhile.TypeCheckCwhile().type_check
typecheck_dict = {
    'source': typecheck_Lwhile,
    'shrink': typecheck_Lwhile,
    'expose_allocation': typecheck_Lwhile,
    'remove_complex_operands': typecheck_Lwhile,
    'explicate_control': typecheck_Cwhile,
}
interpLwhile = interp_Lwhile.InterpLwhile().interp
interpCwhile = interp_Cif.InterpCif().interp
interp_dict = {
    'shrink': interpLwhile,
    'expose_allocation': interpLwhile,
    'remove_complex_operands': interpLwhile,
    'explicate_control': interpCwhile,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

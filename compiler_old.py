import os
import copy
import logging
import logzero
import argparse
import sympy

from wfomc import parse_input
from wfomc.problems import WFOMCProblem
from wfomc.fol.syntax import Const, X, Y
from wfomc.cell_graph.cell_graph import Cell, AtomicFormula

from utils import NodeType, create_node, Node, print_circuit

import context
from context import EXT_PRED_PREFIX, conditional_on_lit, remove_aux_atom, substitute


class RecursionState:
    def __init__(self, block_status: dict[Const, list[bool]],
                 candidate_witness: dict[Const, list[list[Const]]], 
                 unprocessed_pair: set[frozenset[Const]], 
                 detetermined_facts: set[str],
                 depth: int = -1):
        
        self.depth = depth
        self.block_status = block_status
        self.unprocessed_pair = unprocessed_pair
        self.candidate_witness = candidate_witness
        self.detetermined_facts = detetermined_facts

    def copy(self):
        return RecursionState(copy.deepcopy(self.block_status), 
                              copy.deepcopy(self.candidate_witness), 
                              copy.deepcopy(self.unprocessed_pair), 
                              copy.deepcopy(self.detetermined_facts), 
                              self.depth)

def parse_args():
    parser = argparse.ArgumentParser(
        description='WFOMC for MLN',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('--input', '-i', type=str, required=True, help='sentence file')
    parser.add_argument('--domain-size', '-n', type=int, required=True, help='domain size')
    parser.add_argument('--debug', action='store_true', default=False)
    args = parser.parse_args()
    return args

def get_problem(args) -> WFOMCProblem:
    problem = parse_input(args.input)
    new_domain: set[Const] = set()
    for i in range(args.domain_size):
        new_domain.add(Const(f'e{i}'))
    problem.domain = new_domain
    return problem

def init_candidate_witness(domain_to_cell: dict[Const, context.Cell], 
                          rel_dict: dict[tuple[Cell, Cell], list[frozenset[AtomicFormula]]],
                          block_status: dict[Const, list[bool]],
                          domain: set[Const]):
    candidate_witness: dict[Const, list[list[Const]]] = {}
    for element in domain:
        candidate_witness[element] = []
        for idx_ext, block in enumerate(block_status[element]):
            if not block:
                candidate_witness[element].append(None)
                continue
            witness_list = []
            for wit in domain:
                if element == wit:
                    continue
                for _, rel in enumerate(rel_dict[(domain_to_cell[element], domain_to_cell[wit])]):
                    for atom in rel:
                        if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive and \
                                int(atom.pred.name[len(EXT_PRED_PREFIX):]) == idx_ext and atom.args[0] == X:
                            witness_list.append(wit)
            assert len(witness_list) != 0
            candidate_witness[element].append(witness_list)
    return candidate_witness

def check_sat(domain_to_cell: dict[Const, Cell],
              get_witness_relation: callable,
              block_status: dict[Const, list[bool]], 
              candidate_witness: dict[Const, list[list[Const]]]) -> bool:
    for ego_element, blocks in block_status.items():
        if not any(blocks):
            continue
        for block_idx, block in enumerate(blocks):
            if not block:
                continue
            if len(candidate_witness[ego_element][block_idx]) == 0:
                return False
            # 先只考虑一个 1-type 的情况
            for witness in candidate_witness[ego_element][block_idx]:
                for (rel, atom) in get_witness_relation(domain_to_cell[ego_element], domain_to_cell[witness], block_idx):
                    block_status_copy = copy.deepcopy(block_status)
                    candidate_witness_copy = copy.deepcopy(candidate_witness)
                    # update block status
                    for atom in rel:
                        if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive:
                            if atom.args[0] == X:
                                block_status_copy[ego_element][int(atom.pred.name[len(EXT_PRED_PREFIX):])] = False
                            else:
                                block_status_copy[witness][int(atom.pred.name[len(EXT_PRED_PREFIX):])] = False
                    # update sat matrix
                    for witness_list in candidate_witness_copy[ego_element]:
                        if witness_list == None:
                            continue
                        witness_list.remove(witness)
                    for witness_list in candidate_witness_copy[witness]:
                        if witness_list == None:
                            continue
                        witness_list.remove(ego_element)

                    if check_sat(domain_to_cell, get_witness_relation, block_status_copy, candidate_witness_copy):
                        return True  
    sat_flag = True
    for blocks in block_status.values():
        if not any(blocks):
            continue
        sat_flag = False
        break 
    return sat_flag

def free_subcircuit_compilation(ctx: context.Context, 
                                unprocessed_pair: set[frozenset[Const]],
                                domain_to_cell: dict[Const, Cell]):
    and_node = create_node(NodeType.AND)
    for pair in unprocessed_pair:
        and_node.children.append(ctx.pair_to_node_index[pair])
    #     or_node = create_node(NodeType.OR)
    #     and_node.children.append(or_node.index)
        
    #     e1, e2 = list(pair)[0], list(pair)[1]
    #     for rel in ctx.rels_of_cells[(domain_to_cell[e1], domain_to_cell[e2])]:
    #         or_node.children.append(ctx.gnd_rel_to_node_index[f'R{ctx.relations.index(rel)}({e1},{e2})'])
    return and_node

def select_witness(ego_element: Const, block_idx: int, 
                   block_status: dict[Const, list[bool]], 
                   candidate_witness: dict[Const, list[list[Const]]]):
    witness_list = candidate_witness[ego_element][block_idx]
    # 1.优先还有 block 的 witness
    # 2.优先按之前的pair order选择witness
    witness_list.sort(
        key=lambda x: (
            not block_status[x][block_idx],
        )
    )
    for witness in witness_list:
        yield witness

def is_isomorphic(state: RecursionState, state_cache: dict[RecursionState, int]):
    for key, value in state_cache.items():
        if state.block_status == key.block_status and \
                state.candidate_witness == key.candidate_witness and \
                state.unprocessed_pair == key.unprocessed_pair:
            return value
    return None

def domain_recursion(ctx: context.Context, domain: list[Const], DomainToCell: dict[Const, Cell],
                     subroot_node: Node, SubCircuits: dict[frozenset[frozenset[Const]], Node], 
                     StateCache: dict[RecursionState, int], rec_state: RecursionState):
    rec_state.depth += 1
    if len(domain) == 0:
        # TODO
        if len(rec_state.unprocessed_pair) != 0:
            if frozenset(rec_state.unprocessed_pair) in SubCircuits.keys():
                remaining_node = SubCircuits[frozenset(rec_state.unprocessed_pair)]
            else:
                remaining_node = free_subcircuit_compilation(ctx, rec_state.unprocessed_pair, DomainToCell)
                SubCircuits[frozenset(rec_state.unprocessed_pair)] = remaining_node
            subroot_node.children.append(remaining_node.index)
        return

    ego_element = domain[0]
    domain = domain[1:]
    print(rec_state.depth * ' ', f'ego_element: {ego_element}')
    
    if not any(rec_state.block_status[ego_element]):
        print(rec_state.depth * ' ', f'no block for {ego_element}, continue')
        domain_recursion(ctx, domain, DomainToCell,
                         subroot_node, SubCircuits, StateCache, rec_state)
        return
    
    for block_idx, block in enumerate(rec_state.block_status[ego_element]):
        if not block:
            continue
        for witness in select_witness(ego_element, block_idx, rec_state.block_status, rec_state.candidate_witness):
            print(rec_state.depth * ' ', f'ego_element: {ego_element}, block_idx: {block_idx}, witness: {witness}')
            ego_cell = DomainToCell[ego_element]
            wit_cell = DomainToCell[witness]
            
            aux_lit = ctx.get_witness_lit(ego_cell, wit_cell, block_idx)
            ng_key_lit = ctx.auxlit_to_orilit[aux_lit]
            key_lit = substitute(ng_key_lit, {X: ego_element, Y: witness})
            
            ng_constrained_lits = conditional_on_lit(ng_key_lit, ctx.rels_of_cells[(ego_cell, wit_cell)])
            ng_constrained_lits = remove_aux_atom(ng_constrained_lits)
            
            if not check_sat(DomainToCell, ctx.get_witness_relation, rec_state.block_status, rec_state.candidate_witness):
                print('nosat ', f'{EXT_PRED_PREFIX}{block_idx}({ego_element},{witness})')
                continue
            
            rec_state_copy = rec_state.copy()
            rec_state_copy.unprocessed_pair.remove(frozenset([ego_element, witness]))
            
            # create the AND node
            and_node = create_node(NodeType.AND)
            subroot_node.children.append(and_node.index)
            
            # add the key literal
            key_lit_leaf_index = create_node(NodeType.LEAF, key_lit.__str__()).index
            and_node.children.append(key_lit_leaf_index)
            rec_state_copy.detetermined_facts.add(key_lit.__str__())
            # update the block status
            rec_state_copy.block_status[ego_element][block_idx] = False
            # update candidate witness
            rec_state_copy.candidate_witness[ego_element][block_idx].remove(witness)
            
            # add the constrained literals
            constrained_sympy_expr = ctx.simplify_dnf(ng_constrained_lits)
            # FIXME
            if constrained_sympy_expr == True:
                pass
            elif constrained_sympy_expr.is_Atom:
                ng_constrained_lit = ctx.sym_to_atom[constrained_sympy_expr]
                constrained_lit = substitute(ng_constrained_lit, {X: ego_element, Y: witness})
                constrained_lit_leaf_index = create_node(NodeType.LEAF, constrained_lit.__str__()).index
                and_node.children.append(constrained_lit_leaf_index)
                
                rec_state_copy.detetermined_facts.add(constrained_lit.__str__())
                tmp_lit = substitute(constrained_lit, {ego_element: Y, witness: X})
                if tmp_lit in ctx.orilit_to_auxlit.keys():
                    wit_block_idx = int(ctx.orilit_to_auxlit[tmp_lit].pred.name[len(EXT_PRED_PREFIX):])
                    
                    if rec_state_copy.block_status[witness][wit_block_idx]:
                        # update the block status
                        rec_state_copy.block_status[witness][wit_block_idx] = False
                        # update candidate witness
                        rec_state_copy.candidate_witness[witness][wit_block_idx].remove(ego_element)
            else:
                for sym in constrained_sympy_expr.atoms():
                    atom = ctx.sym_to_atom[sym]
                    # for ego element:
                    atom_ego = substitute(atom, {ego_element: X, witness: Y})
                    if atom_ego in ctx.orilit_to_auxlit.keys():
                        wit_block_idx = int(atom_ego.pred.name[len(EXT_PRED_PREFIX):])
                        if atom_ego.positive:
                            rec_state_copy.block_status[ego_element][wit_block_idx] = False
                        rec_state_copy.candidate_witness[ego_element][wit_block_idx].remove(witness)
                    # for witness:
                    atom_wit = substitute(atom, {ego_element: Y, witness: X})
                    if atom_wit in ctx.orilit_to_auxlit.keys():
                        wit_block_idx = int(atom_wit.pred.name[len(EXT_PRED_PREFIX):])
                        if atom_wit.positive:
                            rec_state_copy.block_status[witness][wit_block_idx] = False
                        rec_state_copy.candidate_witness[witness][wit_block_idx].remove(ego_element)                        
            
            # add the OR node for remaining (cache first)
            isomorphic_index = is_isomorphic(rec_state_copy, StateCache) 
            if isomorphic_index is not None:
                print(f'{rec_state_copy.detetermined_facts} ---------> isomorphic_path')
                and_node.children.append(isomorphic_index)
            else:
                new_subroot_node = create_node(NodeType.OR)
                and_node.children.append(new_subroot_node.index)
                StateCache[rec_state_copy] = new_subroot_node.index
                
                print(rec_state.depth * ' ', f'block_status: {rec_state_copy.block_status}')
                domain_recursion(ctx, domain, DomainToCell, new_subroot_node, 
                                    SubCircuits, StateCache, rec_state_copy)
        
            # 如果 key_lit 不成立会产生额外的‘限制’，那么应该对其不成立的情况进行分支考虑
            # 这个‘限制’很重要，有可能会大大缩小 subcircuit 的大小
            # 当然，有可能这个‘限制’也可能需要满足其他的要求，比如这个‘限制’排除了其他 element 的 witness 备选集
            
            reverse_ng_key_lit = ng_key_lit.__invert__()
            ng_constrained_lits = conditional_on_lit(reverse_ng_key_lit, ctx.rels_of_cells[(ego_cell, wit_cell)])
            ng_constrained_lits = remove_aux_atom(ng_constrained_lits)
            
            key_lit = substitute(reverse_ng_key_lit, {X: ego_element, Y: witness})
            
            rec_state_copy = rec_state.copy()
            rec_state_copy.unprocessed_pair.remove(frozenset([ego_element, witness]))
            
            if ego_element in rec_state_copy.candidate_witness[witness][block_idx]:  # 限制条件
                rec_state_copy.candidate_witness[ego_element][block_idx].remove(witness)
                rec_state_copy.candidate_witness[witness][block_idx].remove(ego_element)
                
                if check_sat(DomainToCell, ctx.get_witness_relation, 
                                rec_state_copy.block_status, rec_state_copy.candidate_witness):
                    
                    # create the AND node
                    and_node = create_node(NodeType.AND)
                    subroot_node.children.append(and_node.index)
                    
                    print(rec_state.depth * ' ', f'consider reverse key lit: {key_lit}')
                    
                    # add the key literal
                    key_lit_leaf_index = create_node(NodeType.LEAF, key_lit.__str__()).index
                    and_node.children.append(key_lit_leaf_index)
                    rec_state_copy.detetermined_facts.add(key_lit.__str__())
                    
                    # add the constrained literals
                    constrained_sympy_expr = ctx.simplify_dnf(ng_constrained_lits)
                    # FIXME
                    if constrained_sympy_expr == True:
                        pass
                    elif constrained_sympy_expr.is_Atom:
                        # lit_leaf_index = ctx.literal_to_node_index[f'{sympy_expr}']
                        ng_constrained_lit = ctx.sym_to_atom[constrained_sympy_expr]
                        constrained_lit = substitute(ng_constrained_lit, {X: ego_element, Y: witness})
                        constrained_lit_leaf_index = create_node(NodeType.LEAF, constrained_lit.__str__()).index
                        and_node.children.append(constrained_lit_leaf_index)
                        rec_state_copy.detetermined_facts.add(constrained_lit.__str__())
                        
                    else:
                        for sym in constrained_sympy_expr.atoms():
                            atom = ctx.sym_to_atom[sym]
                            # for ego element:
                            atom_ego = substitute(atom, {ego_element: X, witness: Y})
                            if atom_ego in ctx.orilit_to_auxlit.keys():
                                wit_block_idx = int(atom_ego.pred.name[len(EXT_PRED_PREFIX):])
                                if atom_ego.positive:
                                    rec_state_copy.block_status[ego_element][wit_block_idx] = False
                                rec_state_copy.candidate_witness[ego_element][wit_block_idx].remove(witness)
                            # for witness:
                            atom_wit = substitute(atom, {ego_element: Y, witness: X})
                            if atom_wit in ctx.orilit_to_auxlit.keys():
                                wit_block_idx = int(atom_wit.pred.name[len(EXT_PRED_PREFIX):])
                                if atom_wit.positive:
                                    rec_state_copy.block_status[witness][wit_block_idx] = False
                                rec_state_copy.candidate_witness[witness][wit_block_idx].remove(ego_element)    
                            
                    # add the OR node for remaining (cache first)
                    isomorphic_index = is_isomorphic(rec_state_copy, StateCache)
                    if isomorphic_index is not None:
                        print(f'{rec_state_copy.detetermined_facts} ---------> isomorphic_path')
                        and_node.children.append(isomorphic_index)
                    else:
                        new_subroot_node = create_node(NodeType.OR)
                        StateCache[rec_state_copy] = new_subroot_node.index
                        and_node.children.append(new_subroot_node.index)
                    
                        domain_recursion(ctx, [ego_element] + domain, DomainToCell, new_subroot_node, 
                                    SubCircuits, StateCache, rec_state_copy)
                        break
                

if __name__ == "__main__":
    # import sys
    # sys.setrecursionlimit(int(1e6))
    args = parse_args()
    if args.debug:
        logzero.loglevel(logging.DEBUG)
    else:
        logzero.loglevel(logging.INFO)

    problem = get_problem(args)    
    ctx = context.Context(problem)
    
    # assign cell to each element in the domain
    DomainToCell: dict[Const, context.Cell] = {}
    for element in ctx.domain:
        DomainToCell[element] = ctx.cells[0]
    
    block_status: dict[Const, list[bool]] = {}
    for element in ctx.domain:
        block_status[element] = copy.deepcopy(ctx.blcok_of_cell[DomainToCell[element]])
    
    
    candidate_witness = init_candidate_witness(DomainToCell, ctx.rels_of_cells, block_status, ctx.domain)
    
    print(DomainToCell)
    print(candidate_witness)
    
    root_node = create_node(NodeType.OR)
    
    unprocessed_pair = set()
    for idx, element in enumerate(ctx.domain):
        for idx_2 in range(idx + 1, len(ctx.domain)):
            if frozenset([element, ctx.domain[idx_2]]) not in unprocessed_pair:
                unprocessed_pair.add(frozenset([element, ctx.domain[idx_2]]))
                
    SubCircuits: dict[frozenset[frozenset[Const]], Node] = {}
    StateCache: dict[RecursionState, int] = {}
    
    rec_state = RecursionState(block_status, candidate_witness, unprocessed_pair, set())
    domain_recursion(ctx, copy.deepcopy(ctx.domain),  DomainToCell, 
                     root_node, SubCircuits, StateCache, rec_state)

    print_circuit(root_node)
        
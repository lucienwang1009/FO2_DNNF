from __future__ import annotations
from logzero import logger
from itertools import combinations, product
from copy import deepcopy
import sympy

from wfomc.fol.syntax import AtomicFormula, Const, Pred, QFFormula, a, b, c, X, Y, QuantifiedFormula, top, bot
from wfomc.problems import WFOMCProblem
from wfomc.fol.sc2 import SC2, to_sc2
from wfomc.fol.utils import new_predicate, exactly_one_qf
from wfomc.cell_graph.cell_graph import CellGraph, Cell, OptimizedCellGraph
from wfomc.cell_graph.utils import conditional_on

from utils import NodeType, create_node, Node, print_circuit

EXT_PRED_PREFIX = '@beta'

def build_two_tables(formula: QFFormula, cells: list[Cell]) -> tuple[list[frozenset[AtomicFormula]], 
                                                                     dict[tuple[Cell, Cell], list[frozenset[AtomicFormula]]]]:
    models = dict()
    gnd_formula: QFFormula = ground_on_tuple(formula, a, b) & ground_on_tuple(formula, b, a)
    gnd_formula = gnd_formula.substitute({a: X, b: Y})
    gnd_lits = gnd_formula.atoms()
    gnd_lits = gnd_lits.union(frozenset(map(lambda x: ~x, gnd_lits)))
    for model in gnd_formula.models():
        models[model] = 1

    two_tables: dict[tuple[Cell, Cell], list[frozenset[AtomicFormula]]] = dict()
    for i, cell in enumerate(cells):
        models_1 = conditional_on(models, gnd_lits, cell.get_evidences(X))
        for j, other_cell in enumerate(cells):
            models_2 = conditional_on(models_1, gnd_lits, other_cell.get_evidences(Y))
            two_tables[(cell, other_cell)] = []
            two_table_list = list(models_2.keys())
            # def sort(rel: list[AtomicFormula]):
            #     res = [0]*ext_pred_num
            #     for atom in rel:
            #         if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.args[0] != atom.args[1] and atom.positive:
            #             res[int(atom.pred.name[len(EXT_PRED_PREFIX):])] = 1
            #     print(res)
            #     return tuple(res)
            # two_table_list.sort(key=sort, reverse=True) # put the relations with more positive ext predicates first
            for model in two_table_list:
                two_tables[(cell, other_cell)].append(frozenset({atom for atom in model if len(atom.args) == 2 and atom.args[0] != atom.args[1]}))
      
    return list(models.keys()), two_tables

def ground_on_tuple(formula: QFFormula, c1: Const, c2: Const = None) -> QFFormula:
        variables = formula.vars()
        if len(variables) > 2:
            raise RuntimeError(
                "Can only ground out FO2"
            )
        if len(variables) == 1:
            constants = [c1]
        else:
            if c2 is not None:
                constants = [c1, c2]
            else:
                constants = [c1, c1]
        substitution = dict(zip(variables, constants))
        gnd_formula = formula.substitute(substitution)
        return gnd_formula

def conditional_on_lit(evi: AtomicFormula, dnf:list[frozenset[AtomicFormula]]) -> list[frozenset[AtomicFormula]]:
    if evi is None:
        return dnf
    conditioned_dnf: list[frozenset[AtomicFormula]] = []
    # remaining_dnf: list[frozenset[AtomicFormula]] = []
    for clause in dnf:
        # evi is positive by default
        clause = set(clause)
        if evi in clause:
            clause.remove(evi)
            conditioned_dnf.append(frozenset(clause))
        # else:
        #     clause.remove(~evi)
        #     remaining_dnf.append(frozenset(clause))
    return conditioned_dnf

def remove_aux_atom(input):
    assert isinstance(input, (frozenset, list, set))
    if isinstance(next(iter(input)), AtomicFormula):
        return type(input)(filter(lambda atom: not atom.pred.name.startswith(EXT_PRED_PREFIX), set(input)))
    elif isinstance(next(iter(input)), (frozenset, list, set)):
        return type(input)(map(lambda clause: remove_aux_atom(clause), input))
    else:
        raise RuntimeError(f'The type of input is not correct: {type(input)}')

def substitute(input, subst):
    if isinstance(input, AtomicFormula):
        return input.substitute(subst)
    assert isinstance(input, (frozenset, list, set))
    if isinstance(next(iter(input)), AtomicFormula):
        return type(input)(map(lambda atom: atom.substitute(subst), input))
    elif isinstance(next(iter(input)), (frozenset, list, set)):
        return type(input)(map(lambda clause: substitute(clause, subst), input))
    else:
        raise RuntimeError(f'The type of input is not correct: {type(input)}')

class Context(object):
    
    def __init__(self, problem: WFOMCProblem):
        self.domain: set[Const] = problem.domain
        self.sentence: SC2 = problem.sentence
        self.weights: dict[Pred, tuple] = problem.weights
        
        # self.domain_: set[int] = set()
        # for e in self.domain:
        #     self.domain_.add(int(e.name[1:]))
        # self.domain = self.domain_
        self.domain_size = len(self.domain)
        self.domain = [Const(f'{i}') for i in range(self.domain_size)]
        
        self.uni_formula: QFFormula = self.sentence.uni_formula
        self.ext_formulas: list[QuantifiedFormula] = []
        self._scott()
        
        self._m = len(self.ext_formulas)
        
        self.cell_graph: CellGraph = CellGraph(self.uni_formula, self.get_weight)
        self.cells: list[Cell] = self.cell_graph.cells
        
        # 2-tables contaion the cells, but the relations are not included
        self.rels_of_cells: dict[tuple[Cell, Cell], list[frozenset[AtomicFormula]]] = {}
        self.two_tables, self.rels_of_cells = build_two_tables(self.uni_formula, self.cells)
        
        self.atom_to_sym: dict[AtomicFormula, sympy.Symbol] = {}
        self.sym_to_atom: dict[sympy.Symbol, AtomicFormula] = {}
        self.relations: list[frozenset[AtomicFormula]] = []
        for two_table in self.two_tables:
            relation: set[AtomicFormula] = set()
            for lit in two_table:
                if lit.args[0] != lit.args[1]:
                    relation.add(lit)
                    atom = lit if lit.positive else ~lit
                    if atom not in self.atom_to_sym and not atom.pred.name.startswith(EXT_PRED_PREFIX):
                        symbol = sympy.Symbol(atom.__str__())
                        self.atom_to_sym[atom] = symbol
                        self.sym_to_atom[symbol] = atom
            self.relations.append(frozenset(relation))
        
        # init the blocks of each cell
        self.blcok_of_cell: dict[Cell, list[bool]] = {}
        for cell in self.cells:
            self.blcok_of_cell[cell] = [True for _ in range(self._m)]
            for pred in cell.preds:
                if pred.name.startswith(EXT_PRED_PREFIX) and cell.is_positive(pred):
                    block_idx = int(pred.name[len(EXT_PRED_PREFIX):])
                    self.blcok_of_cell[cell][block_idx] = False
        
        # init the leaf nodes
        self.literal_to_node_index: dict[str, int] = {}
        self.node_index_to_literal: dict[int, str] = {}
        self.gnd_rel_to_node_index: dict[str, int] = {}
        self.pair_to_node_index: dict[frozenset[Const], int] = {}
        
        for (e_1, e_2) in combinations(self.domain, 2):
            element_pair = f'({e_1.name},{e_2.name})'
            r_element_pair = f'({e_2.name},{e_1.name})'
            
            for pred in self.cells[0].preds:
                if pred.name.startswith(EXT_PRED_PREFIX) or pred.arity != 2:
                    continue
                leaf_node = create_node(NodeType.LEAF, f'{pred.name}{element_pair}')
                self.literal_to_node_index[leaf_node.literal_str] = leaf_node.index
                self.node_index_to_literal[leaf_node.index] = leaf_node.literal_str
                
                leaf_node = create_node(NodeType.LEAF, f'{pred.name}{r_element_pair}')
                self.literal_to_node_index[leaf_node.literal_str] = leaf_node.index
                self.node_index_to_literal[leaf_node.index] = leaf_node.literal_str
                
                leaf_node = create_node(NodeType.LEAF, f'~{pred.name}{element_pair}')
                self.literal_to_node_index[leaf_node.literal_str] = leaf_node.index
                self.node_index_to_literal[leaf_node.index] = leaf_node.literal_str
                
                leaf_node = create_node(NodeType.LEAF, f'~{pred.name}{r_element_pair}')
                self.literal_to_node_index[leaf_node.literal_str] = leaf_node.index
                self.node_index_to_literal[leaf_node.index] = leaf_node.literal_str
            
            or_node = create_node(NodeType.OR)
            self.pair_to_node_index[frozenset([e_1, e_2])] = or_node.index
            for rel in self.relations:
                and_node = create_node(NodeType.AND)
                or_node.children.add(and_node.index)
                for lit in rel:
                    if lit.pred.name.startswith(EXT_PRED_PREFIX) or lit.args[0] == lit.args[1]:
                        continue
                    positive = '' if lit.positive else '~'
                    if lit.args[0] == X and lit.args[1] == Y:
                        and_node.children.add(self.literal_to_node_index[f'{positive}{lit.pred.name}{element_pair}'])
                    elif lit.args[0] == Y and lit.args[1] == X:
                        and_node.children.add(self.literal_to_node_index[f'{positive}{lit.pred.name}{r_element_pair}'])
                    else:
                        raise RuntimeError(f'The the arguments is not correct: {lit.args[0]}, {lit.args[1]}')
                self.gnd_rel_to_node_index[f'R{self.relations.index(rel)}({e_1},{e_2})'] = and_node.index
                self.gnd_rel_to_node_index[f'R{self.relations.index(rel)}({e_2},{e_1})'] = and_node.index
            
        # construct 2-table subcircuits
        # 每对cell的每个2-table都对应一个子电路
        self.subcircuits_of_rels: dict[tuple[Cell, Cell],
                                       dict[tuple[tuple, tuple], 
                                            dict[tuple[Const, Const], int]]] = {}
        self.init_subcircuits_of_rels()
    
    # neccessary paraneter for CellGraph function     
    def get_weight(self, pred: Pred) -> tuple:
        default = 1
        if pred in self.weights:
            return self.weights[pred]
        return (default, default)
    
    def get_witness_relation(self, ego_element_cell: Const, witness_cell: Const, block_idx: int) \
        -> list[tuple[frozenset[AtomicFormula],AtomicFormula]]:
        result = []
        for rel in self.rels_of_cells[(ego_element_cell, witness_cell)]:
            for atom in rel:
                if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive and \
                        int(atom.pred.name[len(EXT_PRED_PREFIX):]) == block_idx and atom.args[0] == X:
                    result.append((rel, atom))
                    break
        return result
    
    def get_witness_lit(self, ego_element_cell: Const, witness_cell: Const, block_idx: int) \
        -> AtomicFormula:
        for rel in self.rels_of_cells[(ego_element_cell, witness_cell)]:
            for atom in rel:
                if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive and \
                        int(atom.pred.name[len(EXT_PRED_PREFIX):]) == block_idx and atom.args[0] == X:
                    return atom
        return None
    
    def _scott(self):
        while(not isinstance(self.uni_formula, QFFormula)):
            self.uni_formula = self.uni_formula.quantified_formula
        
        # FIXME: this is a hack to map the auxiliary predicates to the original formulas
        self.auxlit_to_orilit: dict[AtomicFormula, AtomicFormula] = {}
        self.orilit_to_auxlit: dict[AtomicFormula, AtomicFormula] = {}

        for formula in self.sentence.ext_formulas:
            quantified_formula = formula.quantified_formula.quantified_formula
            new_pred = new_predicate(2, EXT_PRED_PREFIX)
            new_atom = new_pred(X,Y)
            
            # FIXME: this is a hack to map the auxiliary predicates to the original formulas
            if isinstance(quantified_formula, AtomicFormula):
                self.auxlit_to_orilit[new_atom] = quantified_formula
                self.orilit_to_auxlit[quantified_formula] = new_atom
            
            formula.quantified_formula.quantified_formula = new_atom
            self.ext_formulas.append(formula)
            self.uni_formula = self.uni_formula.__and__(new_atom.equivalent(quantified_formula))

        logger.info('The universal formula: \n%s', self.uni_formula)
        logger.info('The existential formulas: \n%s', self.ext_formulas)
        
    def simplify_dnf(self, dnf: set[frozenset[AtomicFormula]]):
        sympy_expr: sympy.Expr = sympy.Or()
        for clause in dnf:
            sympy_clause_expr = sympy.And()
            for lit in clause:
                if lit.positive:
                    sympy_clause_expr = sympy.And(sympy_clause_expr, self.atom_to_sym[lit])
                else:
                    sympy_clause_expr = sympy.And(sympy_clause_expr, ~self.atom_to_sym[~lit])
            sympy_expr = sympy.Or(sympy_expr, sympy_clause_expr)
        sympy_expr = sympy.simplify_logic(sympy_expr)
        # TODO: convert the sympy expression to the formula
        # formula: QFFormula = top        
        return sympy_expr
    
    def init_subcircuits_of_rels(self):
        for cell_pair, rels in self.rels_of_cells.items():
            self.subcircuits_of_rels[cell_pair] = {}
            # classify the relations according to the blocks
            block_to_rel: dict[tuple[tuple, tuple], set[frozenset[AtomicFormula]]] = {}
            for rel in rels: # rel don't include the cell literals
                break_blocks_1, break_blocks_2 = [False for _ in range(self._m)], [False for _ in range(self._m)]
                for lit in rel:
                    if lit.pred.name.startswith(EXT_PRED_PREFIX) and lit.positive:
                        block_idx = int(lit.pred.name[len(EXT_PRED_PREFIX):])
                        if lit.args[0] == X:
                            break_blocks_1[block_idx] = True
                        elif lit.args[0] == Y:
                            break_blocks_2[block_idx] = True
                        else:
                            raise RuntimeError(f'The arguments of the atom is not correct: {lit}')
                break_block: tuple[tuple, tuple] = (tuple(break_blocks_1), tuple(break_blocks_2))
                if break_block not in block_to_rel:
                    block_to_rel[break_block] = set()
                block_to_rel[break_block].add(rel)
            
            # construct the subcircuit for rels corresponding to the break_block
            for break_block, rels in block_to_rel.items():
                self.subcircuits_of_rels[cell_pair][break_block] = {}
                if len(rels) == 0:
                    raise RuntimeError('The length of rels is 0')
                expr = self.simplify_dnf(remove_aux_atom(rels))
                
                def extract_clauses(cnf_expr):
                    if isinstance(cnf_expr, sympy.And):
                        clauses = cnf_expr.args
                    else:
                        clauses = [cnf_expr]
                    return clauses
                def extract_literals(clause):
                    if isinstance(clause, sympy.Or):
                        return [~self.sym_to_atom[~lit] if isinstance(lit, sympy.Not) else self.sym_to_atom[lit] for lit in clause.args]
                    else:
                        return [~self.sym_to_atom[~clause] if isinstance(clause, sympy.Not) else self.sym_to_atom[clause]]
                clauses = [extract_literals(clause) for clause in extract_clauses(expr)]
                
                for element_pair in product(self.domain, repeat=2):
                    e_1, e_2 = element_pair
                    if e_1 == e_2:
                        continue
                    if cell_pair[0] == cell_pair[1] and \
                        (e_2, e_1) in self.subcircuits_of_rels[cell_pair][break_block].keys():
                        self.subcircuits_of_rels[cell_pair][break_block][element_pair] = self.subcircuits_of_rels[cell_pair][break_block][(e_2, e_1)]
                        continue
                    and_node = create_node(NodeType.AND)
                    for clause in clauses:
                        if len(clause) == 1:
                            lit = clause[0].substitute({X: e_1, Y: e_2})
                            and_node.children.add(self.literal_to_node_index[lit.__str__()])
                        else:
                            or_node = create_node(NodeType.OR)
                            and_node.children.add(or_node.index)
                            for lit in clause:
                                lit = lit.substitute({X: e_1, Y: e_2})
                                or_node.children.add(self.literal_to_node_index[lit.__str__()])
                    self.subcircuits_of_rels[cell_pair][break_block][element_pair] = and_node.index
    
    def get_wit_subcircuit(self, cell_pair: tuple[Cell, Cell], element_pair: tuple[Const, Const], block_index: int):
        for break_block in self.subcircuits_of_rels[cell_pair].keys():
            if break_block[0][block_index]:
                yield self.subcircuits_of_rels[cell_pair][break_block][element_pair], break_block
from enum import Enum
from wfomc.fol.syntax import Const

import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_agraph import graphviz_layout

class NodeType(Enum):
    AND = 'and'
    OR = 'or'
    LEAF = 'leaf'
    
    def __str__(self):
        return self.value

class Node:
    def __init__(self, type: NodeType, value = None, mark = None):
        self.type = type
        self.mark = mark
        self.children: set[int] = set()
        self.parents: set[int] = set()
        self.literal_str = None
        if type == NodeType.LEAF:
            self.literal_str = value
        
        global NODES
        self.index = len(NODES)
        NODES.append(self)
        
        self.status: dict[Const, any] = {}
    
    def __str__(self):
        if self.type == NodeType.LEAF:
            return f'{self.index} L {self.literal_str}'
        else:
            return f'{self.index} {self.type} {self.children} {self.parents} {self.mark}'

LEAF_DICT: dict[str, Node] = {}
EDGES = []
NODES: list[Node] = []

def create_node(type: NodeType, value: int = None, mark: str = None):
    return Node(type, value, mark)

def update_grobal_nodes(to_remove: list[int]):
    global NODES
    new_nodes = []
    index_map: dict[int, int] = {} 
    for idx, node in enumerate(NODES):
        if idx in to_remove:
            continue
        node.index = len(new_nodes)
        index_map[idx] = node.index
        new_nodes.append(node)
    
    NODES = new_nodes
    for node in NODES:
        new_children = set()
        for child in node.children:
            assert child in index_map
            if child in index_map:
                new_children.add(index_map[child])
        node.children = new_children
        new_parents = set()
        for parent in node.parents:
            assert parent in index_map
            if parent in index_map:
                new_parents.add(index_map[parent])
        node.parents = new_parents

def print_circuit(root_node: Node):
    global NODES
    
    # init parents according to the children
    for node in NODES:
        for child in node.children:
            NODES[child].parents.add(node.index)
            
    for node in NODES:
        print(node)
        
    
    to_remove = []
    # remove the junction nodes that have no children
    for idx, node in enumerate(NODES):
        if node.type == NodeType.LEAF:
            continue
        if len(node.children) != 0:
            continue
        to_remove.append(idx)
        redundant_node_index = node.index
        for parent in node.parents:
            NODES[parent].children.remove(redundant_node_index)
    
    update_grobal_nodes(to_remove)
    to_remove.clear()
    
    # remove the isolated gate nodes
    for node in NODES:
        if len(node.parents) == 0 and node != root_node:
            to_remove.append(node.index)
            # TODO: recursively remove the children
            def dfs(node: Node):
                if len(node.children) == 0:
                    return
                for child in node.children:
                    dfs(NODES[child])
                    NODES[child].parents.remove(node.index)
                    if len(NODES[child].parents) == 0:
                        to_remove.append(NODES[child].index)
            dfs(node)
    
    update_grobal_nodes(to_remove)
    to_remove.clear()
    
    # recursive remove the junction nodes that have only one child
    def remove_nodes_with_one_child(node: Node):
        if node.type == NodeType.LEAF:
            return
        if len(node.children) == 1:
            to_remove.append(node.index)
            unique_child = next(iter(node.children))
            NODES[unique_child].parents.remove(node.index)
            for parent in node.parents:
                NODES[parent].children.remove(node.index)
                NODES[parent].children.add(unique_child)
                NODES[unique_child].parents.add(parent)
            node.children.clear()
            node.parents.clear()
            remove_nodes_with_one_child(NODES[unique_child])
        else:
            for child in node.children:
                remove_nodes_with_one_child(NODES[child])
    remove_nodes_with_one_child(root_node)
    
    update_grobal_nodes(to_remove)
    to_remove.clear()
    
    for node in NODES:
        print(node)
    
    # recursive remove the junction nodes that have the same children
    redundent_node: dict[frozenset, int] = {}
    def remove_nodes_with_same_children(node: Node):
        if node.type == NodeType.LEAF:
            return
        if frozenset(node.children) in redundent_node.keys() and node.index != redundent_node[frozenset(node.children)]:
            substitute_node_index = redundent_node[frozenset(node.children)]
            to_remove.append(node.index)
            for parent in node.parents:
                NODES[parent].children.remove(node.index)
                NODES[parent].children.add(substitute_node_index)
                NODES[substitute_node_index].parents.add(parent)
            for child in node.children:
                NODES[child].parents.remove(node.index)
            node.children.clear()
            node.parents.clear()
        else:
            redundent_node[frozenset(node.children)] = node.index
        for child in node.children:
            remove_nodes_with_same_children(NODES[child])
    remove_nodes_with_same_children(root_node)
    
    update_grobal_nodes(to_remove)
    to_remove.clear()
    
    # for node in NODES:
    #     if node.type == NodeType.LEAF:
    #         continue
    #     if frozenset(node.children) in redundent_node:
    #         to_remove.append(node.index)
    #         for child in node.children:
    #             NODES[child].parents.remove(node.index)
    #             NODES[child].parents.add(redundent_node[frozenset(node.children)])
    #         for parent in node.parents:
    #             NODES[parent].children.remove(node.index)
    #             NODES[parent].children.add(redundent_node[frozenset(node.children)])
    #     else:
    #         redundent_node[frozenset(node.children)] = node.index
    
    # for node in NODES:
    #     print(node)
    
    circuit_size = 0
    gate_count = 0
    for idx, node in enumerate(NODES):
        circuit_size += len(node.children)
        if node.type == NodeType.AND or node.type == NodeType.OR:
            gate_count += 1
    print('Circuit size:', circuit_size)
    print(f'Node count: {len(NODES)}({gate_count} gates)')

    G = nx.DiGraph()

    for node in NODES:
        if node.type == NodeType.LEAF:
            G.add_node(str(node.index), label=node.literal_str)
        elif node.type == NodeType.AND:
            G.add_node(str(node.index), label=f'⋀({node.mark})' if node.mark is not None else '⋀')
        elif node.type == NodeType.OR:
            G.add_node(str(node.index), label=f'⋁({node.mark})' if node.mark is not None else '⋁')
        else:
            raise RuntimeError('The node type is not correct')
        
    for node in NODES:
        for child in node.children:
            G.add_edge(str(node.index), str(child))

    labels = nx.get_node_attributes(G, 'label')
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos,
            with_labels=True, 
            labels=labels, 
            node_color='lightblue', 
            arrows=True, 
            arrowstyle='-', 
            arrowsize=12, 
            node_size=1500, 
            font_size=10,
            verticalalignment='bottom')
    plt.tight_layout()
    plt.show()
    dot_filename = "dnnf.dot"
    nx.nx_agraph.write_dot(G, dot_filename)

    
    
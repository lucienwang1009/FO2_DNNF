import networkx as nx
import matplotlib.pyplot as plt

def parse_circuit_to_networkx(file_path):
    """
    Parse an circuit file and build a NetworkX DiGraph.
    :param file_path: Path to the file
    :return: A networkx.DiGraph with node attributes 'label' and 'shape'
    """
    G = nx.DiGraph()

    with open(file_path, 'r') as f:
        lines = [line.strip() for line in f if line.strip() and not line.startswith('c')]
    # Skip the header line with statistics
    node_lines = lines[1:]

    # Temporary storage of parsed nodes
    node_children = {}
    for idx, line in enumerate(node_lines):
        tokens = line.split()
        kind = tokens[0]
        if kind == 'L':
            label = tokens[1]
            shape = 'oval'
            children = []
        elif kind == 'A':
            k = int(tokens[1])
            children = list(map(int, tokens[2:2 + k]))
            label = '⋀'
            shape = 'box'
        elif kind == 'O':
            branch_idx = tokens[1]
            k = int(tokens[2])
            children = list(map(int, tokens[3:3 + k]))
            # label = f"OR[{branch_idx}]"
            label = '⋁'
            shape = 'diamond'
        elif kind == 'B':
            k = int(tokens[1])
            children = list(map(int, tokens[2:2 + k]))
            label = '⋀'
            shape = 'diamond'
        else:
            raise ValueError(f"Unknown node type: {kind}")

        G.add_node(idx, label=label, shape=shape)
        node_children[idx] = children

    for parent, children in node_children.items():
        for child in children:
            G.add_edge(parent, child)

    return G

def apply_label_mapping(G, map_file):
    """
    Replace leaf-node labels based on a mapping file.
    map_file: path to file whose first two non-comment lines give strings and integers.
    """
    # Read non-comment lines
    with open(map_file, 'r') as f:
        lines = [l.strip() for l in f if l.strip() and l.startswith('c')]
    if len(lines) < 2:
        raise ValueError("Mapping file must contain at least two non-comment lines.")
    header_tokens = lines[0].split()[1:]  # Skip the first token (usually 'c')
    id_tokens = lines[1].split()[1:]
    if len(header_tokens) != len(id_tokens):
        raise ValueError("Header and ID counts do not match in mapping file.")

    mapping = {int(id_tokens[i]): header_tokens[i] for i in range(len(id_tokens))}

    # Update labels for leaf nodes
    for n, data in G.nodes(data=True):
        if data.get('shape') == 'oval':  # leaf
            orig = int(data['label'])
            if orig > 0:
                new_label = mapping.get(orig, data['label'])
            else:
                new_label = f"!{mapping.get(abs(orig), str(abs(orig)))}"
            G.nodes[n]['label'] = new_label
    

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='Parse circuit into a NetworkX DiGraph')
    parser.add_argument('--input', '-i',help='Path to the file')
    args = parser.parse_args()

    G = parse_circuit_to_networkx(f'{args.input}.cir')
    print(f"Graph loaded: {G.number_of_nodes()} nodes, {G.number_of_edges()} edges")
    
    # Remove isolated nodes
    isolates = list(nx.isolates(G))
    if isolates:
        G.remove_nodes_from(isolates)
        print(f"Removed {len(isolates)} isolated nodes: {isolates}")
    
    apply_label_mapping(G, f'{args.input}.cnf')
    
    # Position nodes with Graphviz dot layout (requires pygraphviz or pydot)
    plt.figure(figsize=(12, 8))
    pos = nx.drawing.nx_agraph.graphviz_layout(G, prog='dot')
    labels = nx.get_node_attributes(G, 'label')
    shapes = nx.get_node_attributes(G, 'shape')

    # Draw nodes by shape type
    unique_shapes = set(shapes.values())
    for shp in unique_shapes:
        ns = [n for n, attr in shapes.items() if attr == shp]
        nx.draw_networkx_nodes(G, pos,
                                nodelist=ns,
                                node_color='lightblue', 
                                node_shape=('o' if shp == 'box' else
                                            'o' if shp == 'oval' else
                                            'o' if shp == 'diamond' else
                                            'o'),
                                node_size=1500)
    nx.draw_networkx_edges(G, pos, arrowsize=12, arrowstyle='-')
    nx.draw_networkx_labels(G, pos, labels)
    
    plt.tight_layout()
    # plt.axis('off')
    plt.show()

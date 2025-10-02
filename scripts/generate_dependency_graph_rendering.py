import os
import graphviz
import random
import math
import requests
from collections import defaultdict
from utils import *
import argparse

primes_hash_str = (19, 2, 1, 7, 5, 3, 11, 13, 17)


def hash_str(s):
    return sum(ord(char) * primes_hash_str[i % len(primes_hash_str)] for i, char in enumerate(s))


def find_agda_files(root_dir):
    """
    Find all .lagda.md files in the git-tracked files under the given directory,
    excluding those directly in the root directory.
    """
    git_tracked_files = get_git_tracked_files()
    agda_files = get_agda_files(git_tracked_files)
    return [str(f) for f in agda_files if f.parts[0] == root_dir and len(f.parts) > 2]


LABEL_COLORS_FALLBACK = {
    'category-theory': 'fbca04',
    'commutative-algebra': '3577BB',
    'domain-theory': 'FCBFF5',
    'elementary-number-theory': '4A6123',
    'finite-algebra': '524F88',
    'finite-group-theory': '9A01E2',
    'foundation': '284530',
    'globular-types': '4A7555',
    'graph-theory': 'CCC0C4',
    'group-theory': '963872',
    'higher-group-theory': 'E79FEE',
    'lists': 'C9D999',
    'literature': '3C3C0A',
    'logic': 'A9CFCE',
    'metric-spaces': '923E82',
    'modal-logic': 'A4DC70',
    'modal-type-theory': 'E45F85',
    'oeis': 'F984EC',
    'order-theory': '533A22',
    'organic-chemistry': '07C851',
    'orthogonal-factorization-systems': '578072',
    'real-numbers': 'B66877',
    'reflection': '000000',
    'ring-theory': '1A1277',
    'set-theory': '98335C',
    'simplicial-type-theory': '8C3F69',
    'species': 'EDA55F',
    'structured-types': '069F6E',
    'synthetic-category-theory': '2FEABE',
    'synthetic-homotopy-theory': 'B0D45A',
    'trees': '0F1D69',
    'type-theories': '610CCA',
    'univalent-combinatorics': 'F70D61',
    'universal-algebra': '5467C3',
    'wild-category-theory': 'E2C12E',
}


def fetch_github_labels(repo):
    """Fetch labels and their colors from a GitHub repository."""
    url = f'https://api.github.com/repos/{repo}/labels'
    labels = {}
    try:
        while url:
            response = requests.get(url)
            response.raise_for_status()
            page_labels = response.json()
            labels.update({label['name']: label['color']
                          for label in page_labels})
            # Check if there is a next page
            url = response.links.get('next', {}).get('url')
    except requests.RequestException as e:
        eprint(f'Failed to fetch GitHub labels: {e}')
        # Fallback to preloaded values
        return LABEL_COLORS_FALLBACK
    return labels


def module_based_color(module_name, label_colors):
    """Generate a color based on the module name using GitHub labels."""
    for label, color in label_colors.items():
        if label == module_name or (label == 'foundation' and module_name == 'foundation-core'):
            return f'#{color}'

    # Fallback to random color generation if no label matches
    base_color = (91, 155, 213)
    seed = hash_str(module_name)
    random.seed(seed)
    variation = [random.randint(-91, 70) for _ in range(3)]
    new_color = tuple(
        min(255, max(0, base_color[i] + variation[i])) for i in range(3))
    return '#{:02X}{:02X}{:02X}'.format(*new_color)


def count_imports(graph):
    """Count the number of times each module is imported."""
    import_counts = defaultdict(int)
    for dependencies in graph.values():
        for dep in dependencies:
            import_counts[dep] += 1
    return import_counts


def build_dependency_graph(root_dir, most_imported_drop_count=20):
    """Construct a dependency graph from Agda files."""
    graph = defaultdict(set)
    file_sizes = {}
    agda_files = find_agda_files(root_dir)

    for file in agda_files:
        module_name = os.path.splitext(os.path.relpath(file, root_dir))[
            0].replace(os.sep, '.')
        module_name = module_name[:module_name.rfind('.')]
        imports = parse_agda_imports(file)
        graph[module_name].update(imports)
        file_sizes[module_name] = count_lines_in_file(file)

    # Convert defaultdict to dict for faster lookup
    graph = dict(graph)

    # Count imports and find top imported modules
    import_counts = count_imports(graph)
    _top_imports = sorted(import_counts, key=import_counts.get, reverse=True)[
        :most_imported_drop_count]
    top_imports = set(_top_imports)

    eprint('Excluding modules:')
    for i, m in enumerate(_top_imports):
        eprint(f'{i+1:>3} ({import_counts[m]:>4} imports) {m}')

    # Remove top modules from the graph
    for module in top_imports:
        if module in graph:
            del graph[module]
        for dependencies in graph.values():
            dependencies.discard(module)

    return graph, file_sizes


def generate_html_legend(label_colors, used_labels, output_file, label_counts):
    """Generate an HTML legend with used namespaces and their colors."""
    sorted_labels = sorted(
        used_labels, key=lambda label: label_counts.get(label, 0), reverse=True)
    with open(output_file, 'w') as f:
        f.write('<div class="art-fredrik-dependency-graph-legend">\n')
        for label in sorted_labels:
            if label in label_colors:
                color = label_colors[label]
                f.write(
                    f'  <pre class="art-fredrik-dependency-graph-label" id="{label}"><span class="art-fredrik-dependency-graph-dot" style="background-color: #{color};"></span>{label}</pre>\n')
        f.write('</div>\n')


def render_graph(graph, file_sizes, output_file, format, repo):
    """Render the dependency graph using Graphviz."""
    # Fetch GitHub labels and colors
    label_colors = fetch_github_labels(repo)
    # eprint("Label colors:", label_colors)

    dot = graphviz.Digraph(engine='sfdp', format=format)
    dot.attr(splines='false', overlap='prism10000',
             bgcolor='#FFFFFF00', K='0.3', repulsiveforce='0.3')  # sfdp

    max_lines = max(file_sizes.values(), default=1)
    eprint('Maximum lines of code:', max_lines)
    node_sizes = {node: max(
        0.05, 0.3 * math.sqrt(file_sizes.get(node, 0) / max_lines)) for node in graph}
    node_colors = {node: module_based_color(
        node[:node.rfind('.')], label_colors) for node in graph}

    used_labels = set()
    label_counts = defaultdict(int)

    for node, dependencies in graph.items():
        node_color = node_colors[node]
        label = node[:node.rfind('.')]
        used_labels.add(label)
        label_counts[label] += 1
        dot.node(node, shape='circle', style='filled', fillcolor=node_color, color='#FFFFFF00',
                 width=str(node_sizes[node]), height=str(node_sizes[node]), label='')
        for dep in dependencies:
            if dep in graph:  # Ensure we're not linking to removed nodes
                edge_color = node_color + '10'
                dot.edge(node, dep, color=edge_color, arrowhead='none')

    # Generate HTML legend
    html_legend_output_file = output_file + '_legend.html'
    generate_html_legend(label_colors, used_labels,
                         html_legend_output_file, label_counts)
    eprint(f'HTML Legend saved as {html_legend_output_file}')

    dot.render(output_file, format=format, cleanup=True)


if __name__ == '__main__':
    root_dir = 'src'
    most_imported_drop_count = 20

    parser = argparse.ArgumentParser(
        description='Generate Agda dependency graph.')
    parser.add_argument('output_file', type=str,
                        help='Path to save the output graph.')
    parser.add_argument('format', type=str, choices=[
                        'svg', 'png', 'pdf'], help='Output format of the graph.')

    args = parser.parse_args()

    graph, file_sizes = build_dependency_graph(
        root_dir, most_imported_drop_count=most_imported_drop_count)
    render_graph(graph, file_sizes, args.output_file,
                 format=args.format, repo=GITHUB_REPO)
    eprint(f'Graph saved as {args.output_file}.{args.format}')

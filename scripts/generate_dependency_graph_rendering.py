import os
import graphviz
import random
import math
import requests
from collections import defaultdict
from utils import find_agda_files, parse_agda_imports, count_lines_in_file
import argparse

primes_hash_str = (19,2,1,7,5,3,11,13,17)
def hash_str(s) :
    return sum(ord(char) * primes_hash_str[i%len(primes_hash_str)] for i,char in enumerate(s))

def fetch_github_labels(repo):
    """Fetch labels and their colors from a GitHub repository."""
    url = f"https://api.github.com/repos/{repo}/labels"
    response = requests.get(url)
    response.raise_for_status()
    labels = response.json()
    return {label['name']: label['color'] for label in labels}

def module_based_color(module_name, label_colors):
    """Generate a color based on the module name using GitHub labels."""
    for label, color in label_colors.items():
        if label == module_name or (label == "foundation" and module_name == "foundation-core"):
            return f"#{color}"

    # Fallback to random color generation if no label matches
    base_color = (91, 155, 213)
    seed = hash_str(module_name)
    random.seed(seed)
    variation = [random.randint(-91, 70) for _ in range(3)]
    new_color = tuple(min(255, max(0, base_color[i] + variation[i])) for i in range(3))
    return "#{:02X}{:02X}{:02X}".format(*new_color)

def count_imports(graph):
    """Count the number of times each module is imported."""
    import_counts = defaultdict(int)
    for dependencies in graph.values():
        for dep in dependencies:
            import_counts[dep] += 1
    return import_counts

def build_dependency_graph(root_dir, min_rank_node=20):
    """Construct a dependency graph from Agda files."""
    graph = defaultdict(set)
    file_sizes = {}
    agda_files = find_agda_files(root_dir)

    for file in agda_files:
        module_name = os.path.splitext(os.path.relpath(file, root_dir))[0].replace(os.sep, ".")
        module_name = module_name[:module_name.rfind('.')]
        imports = parse_agda_imports(file)
        graph[module_name].update(imports)
        file_sizes[module_name] = count_lines_in_file(file)

    # Convert defaultdict to dict for faster lookup
    graph = dict(graph)

    # Count imports and find top imported modules
    import_counts = count_imports(graph)
    _top_imports = sorted(import_counts, key=import_counts.get, reverse=True)[:min_rank_node]
    top_imports = set(_top_imports)

    print("Excluding modules:")
    for i, m in enumerate(_top_imports):
        print(f"{i+1:>3} ({import_counts[m]:>3} imports) {m}")

    # Remove top modules from the graph
    for module in top_imports:
        if module in graph:
            del graph[module]
        for dependencies in graph.values():
            dependencies.discard(module)

    return graph, file_sizes

def average_color(color1, color2):
    """Calculate the average color between two hex colors."""
    color1_rgb = tuple(int(color1[i:i+2], 16) for i in (1, 3, 5))
    color2_rgb = tuple(int(color2[i:i+2], 16) for i in (1, 3, 5))
    avg_rgb = tuple((c1 + c2) // 2 for c1, c2 in zip(color1_rgb, color2_rgb))
    return "#{:02X}{:02X}{:02X}".format(*avg_rgb)

def render_graph(graph, file_sizes, output_file, format, repo):
    """Render the dependency graph using Graphviz."""
    # Fetch GitHub labels and colors
    label_colors = fetch_github_labels(repo)

    dot = graphviz.Digraph(engine="sfdp", format=format)
    dot.attr(splines="false", overlap="prism10000", bgcolor="#00000000", K="0.3", repulsiveforce="0.3") #sfdp

    max_lines = max(file_sizes.values(), default=1)
    node_sizes = {node: max(0.05, 0.3 * math.sqrt(file_sizes.get(node, 0) / max_lines)) for node in graph}
    node_colors = {node: module_based_color(node[:node.rfind(".")], label_colors) for node in graph}

    for node, dependencies in graph.items():
        node_color = node_colors[node]
        dot.node(node, shape="circle", style="filled", fillcolor=node_color, color="#00000000", width=str(node_sizes[node]), height=str(node_sizes[node]), label="")
        for dep in dependencies:
            if dep in graph:  # Ensure we're not linking to removed nodes
                # dep_color = node_colors[dep]
                # edge_color =  average_color(node_color, dep_color) + "10"
                edge_color =  node_color + "10"
                dot.edge(node, dep, color=edge_color, arrowhead="none")

    dot.render(output_file, format=format, cleanup=True)
    print(f"Graph saved as {output_file}.{format}")

if __name__ == "__main__":
    repo = "unimath/agda-unimath"
    root_dir = "src"
    min_rank_imports = 20

    parser = argparse.ArgumentParser(description="Generate Agda dependency graph.")
    parser.add_argument("output_file", type=str, help="Path to save the output graph.")
    parser.add_argument("format", type=str, choices=["svg", "png", "pdf"], help="Output format of the graph.")
    parser.add_argument("--min_rank_imports", type=int, default=20, help="Number of top imported files to exclude from the graph.")

    args = parser.parse_args()

    graph, file_sizes = build_dependency_graph(root_dir, min_rank_node=min_rank_imports)
    render_graph(graph, file_sizes, args.output_file, format=args.format, repo=repo)
    print(f"Graph saved as {args.output_file}.{args.format}")

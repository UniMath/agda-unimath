import os
import re
import graphviz
import random
import math
import requests
from collections import defaultdict

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

    # raise Exception(f"There is no label for {module_name}.")
    # Fallback to random color generation if no label matches
    base_color = (91, 155, 213)
    seed = hash_str(module_name)
    random.seed(seed)
    variation = [random.randint(-91, 70) for _ in range(3)]
    new_color = tuple(min(255, max(0, base_color[i] + variation[i])) for i in range(3))
    return "#{:02X}{:02X}{:02X}".format(*new_color)

def find_agda_files(root_dir):
    """
    Recursively find all .lagda.md files in subdirectories of the given directory.
    """
    agda_files = []
    for dirpath, _, filenames in os.walk(root_dir):
        if dirpath == root_dir:
            continue  # Skip files directly in the root directory
        for file in filenames:
            if file.endswith(".lagda.md"):
                agda_files.append(os.path.join(dirpath, file))
    return agda_files

def parse_imports(agda_file):
    """Extract import statements from an Agda file."""
    imports = set()
    with open(agda_file, "r", encoding="utf-8") as f:
        for line in f:
            match = re.match(r"^\s*open\s+import\s+([A-Za-z0-9\-.]+)", line)
            if match:
                imports.add(match.group(1))
    return imports

def count_lines_of_code(file_path):
    """Count lines of code in a file."""
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            return sum(1 for _ in f)
    except Exception:
        return 0

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
        imports = parse_imports(file)
        graph[module_name].update(imports)
        file_sizes[module_name] = count_lines_of_code(file)

    # Convert defaultdict to dict for faster lookup
    graph = dict(graph)

    # Count imports and find top 20 most imported modules
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
    root_directory = "src"
    repo = "unimath/agda-unimath"
    min_rank_imports = 20 # Exclude top 20 imported files
    graph, file_sizes = build_dependency_graph(root_directory, min_rank_node=min_rank_imports)
    render_graph(graph, file_sizes, "website/images/agda_dependency_graph", format="svg", repo=repo)

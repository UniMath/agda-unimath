import os
import re
import graphviz
import random
import math
from collections import defaultdict

def module_based_color(module_name):
    """Generate a color based on the module name."""
    base_color = (91, 155, 213)  # RGB for #5B9BD5
    seed = sum(ord(char) for char in module_name)  # Use a fixed seed based on the module name
    random.seed(seed)
    variation = [random.randint(-60, 60) for _ in range(3)]
    new_color = tuple(min(255, max(0, base_color[i] + variation[i])) for i in range(3))
    return "#{:02X}{:02X}{:02X}".format(*new_color)

def find_agda_files(root_dir):
    """Recursively find all .lagda.md files in subdirectories of the given directory."""
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

def build_dependency_graph(root_dir):
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

    return graph, file_sizes

def average_color(color1, color2):
    """Calculate the average color between two hex colors."""
    color1_rgb = tuple(int(color1[i:i+2], 16) for i in (1, 3, 5))
    color2_rgb = tuple(int(color2[i:i+2], 16) for i in (1, 3, 5))
    avg_rgb = tuple((c1 + c2) // 2 for c1, c2 in zip(color1_rgb, color2_rgb))
    return "#{:02X}{:02X}{:02X}".format(*avg_rgb)

def render_graph(graph, file_sizes, output_file="dependency_graph", format="png"):
    """Render the dependency graph using a faster Graphviz engine."""
    dot = graphviz.Digraph(engine="fdp", format=format)
    dot.attr(splines="true", overlap="prism", K="1.5", bgcolor="white")

    max_lines = max(file_sizes.values(), default=1)
    node_sizes = {node: max(0.04, 0.2 * math.sqrt(file_sizes.get(node, 0) / max_lines)) for node in graph}
    node_colors = {node: module_based_color(node[:node.rfind(".")]) for node in graph}

    for node, dependencies in graph.items():
        node_color = node_colors[node]
        dot.node(node, shape="circle", style="filled", fillcolor=node_color, color="#00000000", width=str(node_sizes[node]), height=str(node_sizes[node]), label="")
        for dep in dependencies:
            if dep in graph:  # Ensure we're not linking to removed nodes
                dep_color = node_colors[dep]
                edge_color = average_color(node_color, dep_color) + "20"
                dot.edge(node, dep, color=edge_color, arrowhead="none")

    dot.render(output_file, format=format, cleanup=True)
    print(f"Graph saved as {output_file}.{format}")

if __name__ == "__main__":
    root_directory = "src"
    graph, file_sizes = build_dependency_graph(root_directory)
    render_graph(graph, file_sizes, "website/images/agda_dependency_graph_" + str(random.randint(0,10000)), format="svg")

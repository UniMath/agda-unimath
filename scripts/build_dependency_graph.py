#!/usr/bin/env python3

import os
import re
import argparse
import json
from collections import defaultdict, deque
from pathlib import Path

# Import utils for Git-related functionality
import sys
import os.path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from scripts.utils import get_git_tracked_files

def find_agda_files(root_dir):
    """Find all Git-tracked Agda source files in the given directory tree."""
    # Get all Git-tracked files
    git_tracked_files = get_git_tracked_files()

    # Filter to keep only Agda files that are tracked by Git
    agda_files = []
    root_path = Path(root_dir).resolve()

    for file_path in git_tracked_files:
        full_path = Path(file_path)
        # Check if the file is in the specified root directory
        if root_path in full_path.resolve().parents or root_path == full_path.resolve().parent:
            if file_path.suffix == '.agda' or (file_path.suffix == '.md' and file_path.stem.endswith('.lagda')):
                agda_files.append(str(file_path))

    return agda_files

def extract_imports(file_path):
    """Extract all module imports from a file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Pattern to match "open import module.name"
    import_pattern = r'open\s+import\s+(\S+)'

    # Find all matches
    imports = re.findall(import_pattern, content)
    return imports

def build_dependency_graph(root_dir):
    """Build a dependency graph from all Git-tracked Agda files in the directory."""
    agda_files = find_agda_files(root_dir)

    # Map each file to its module name (derived from path)
    file_to_module = {}
    for file_path in agda_files:
        # Convert file path to module name
        rel_path = os.path.relpath(file_path, root_dir)
        # Remove extension and replace / with .
        if rel_path.endswith('.lagda.md'):
            module_name = rel_path[:-9]
        else:  # .agda
            module_name = rel_path[:-5]
        module_name = module_name.replace('/', '.')
        file_to_module[file_path] = module_name

    # Invert the mapping for lookup
    module_to_file = {v: k for k, v in file_to_module.items()}

    # Build the dependency graph
    graph = defaultdict(list)
    for file_path in agda_files:
        module_name = file_to_module[file_path]
        imports = extract_imports(file_path)
        for imported_module in imports:
            graph[module_name].append(imported_module)

    return graph, module_to_file

def compute_transitive_closure(graph):
    """
    Compute the transitive closure of the dependency graph.
    Returns a new graph where each module has a list of all its
    direct and indirect dependencies.
    """
    transitive_closure = defaultdict(set)

    # For each module, perform BFS to find all dependencies
    for module in graph:
        queue = deque(graph[module])
        visited = set(graph[module])

        while queue:
            dep = queue.popleft()
            transitive_closure[module].add(dep)

            # Add any dependencies of this dependency that we haven't seen yet
            for next_dep in graph.get(dep, []):
                if next_dep not in visited:
                    visited.add(next_dep)
                    queue.append(next_dep)

    # Convert sets back to lists for consistent output
    return {module: list(deps) for module, deps in transitive_closure.items()}

def export_to_dot(graph, output_file):
    """Export the graph to DOT format for visualization with Graphviz."""
    with open(output_file, 'w') as f:
        f.write('digraph Dependencies {\n')
        f.write('  node [shape=box];\n')

        for module, deps in graph.items():
            for dep in deps:
                f.write(f'  "{module}" -> "{dep}";\n')

        f.write('}\n')

def export_to_json(graph, output_file):
    """Export the graph to JSON format."""
    with open(output_file, 'w') as f:
        json.dump(graph, f, indent=2)

def find_dependent_modules(graph, target_module):
    """
    Find all modules that depend on the target module.
    Uses the transitive closure of the dependency graph.

    Args:
        graph: The transitive closure of the dependency graph
        target_module: The module to check dependencies for

    Returns:
        A list of modules that depend on the target module
    """
    dependent_modules = []
    for module, dependencies in graph.items():
        if target_module in dependencies:
            dependent_modules.append(module)
    return dependent_modules

def main():
    parser = argparse.ArgumentParser(description='Build dependency graph of Agda modules')
    parser.add_argument('root_dir', help='Root directory of the Agda library')
    parser.add_argument('--dot', help='Output file for DOT graph')
    parser.add_argument('--json', help='Output file for JSON representation')
    parser.add_argument('--transitive', action='store_true',
                        help='Compute transitive closure of dependencies')
    parser.add_argument('--transitive-dot', help='Output file for transitive closure DOT graph')
    parser.add_argument('--transitive-json', help='Output file for transitive closure JSON')
    parser.add_argument('--top-dependent', type=int, default=10,
                        help='Print top N modules with most dependencies (default: 10)')
    parser.add_argument('--find-dependents', metavar='MODULE',
                        help='Find all modules that depend on the specified module')
    parser.add_argument('--quiet', action='store_true',
                        help='Suppress informational output, only show requested results')
    # Remove the --omit-top-level argument as we'll always do this
    args = parser.parse_args()

    # If find_dependents is used, enable quiet mode by default unless explicitly overridden
    quiet_mode = args.quiet or (args.find_dependents and not any([args.transitive, args.dot, args.json, args.transitive_dot, args.transitive_json]))

    if not quiet_mode:
        print(f"Analyzing Git-tracked Agda files in {args.root_dir}...")
    graph, module_to_file = build_dependency_graph(args.root_dir)

    if not quiet_mode:
        print(f"Found {len(graph)} tracked modules with dependencies.")

    if args.dot:
        export_to_dot(graph, args.dot)
        if not quiet_mode:
            print(f"DOT graph exported to {args.dot}")

    if args.json:
        export_to_json(graph, args.json)
        if not quiet_mode:
            print(f"JSON data exported to {args.json}")

    # Compute transitive closure if needed
    transitive_graph = None
    if args.transitive or args.transitive_dot or args.transitive_json or args.find_dependents:
        if not quiet_mode:
            print("Computing transitive closure of dependencies...")
        transitive_graph = compute_transitive_closure(graph)

        if args.transitive_dot:
            export_to_dot(transitive_graph, args.transitive_dot)
            if not quiet_mode:
                print(f"Transitive closure DOT graph exported to {args.transitive_dot}")

        if args.transitive_json:
            export_to_json(transitive_graph, args.transitive_json)
            if not quiet_mode:
                print(f"Transitive closure JSON exported to {args.transitive_json}")

        if args.transitive and not (args.transitive_dot or args.transitive_json) and not quiet_mode:
            # Print some statistics about the transitive closure
            avg_deps = sum(len(deps) for deps in transitive_graph.values()) / len(transitive_graph) if transitive_graph else 0
            max_deps = max(len(deps) for deps in transitive_graph.values()) if transitive_graph else 0

            print(f"\nTransitive closure statistics:")
            print(f"  Average dependencies per module: {avg_deps:.2f}")
            print(f"  Maximum dependencies for a module: {max_deps}")

            # Find module with most dependencies (among non-top-level modules)
            non_top_level_modules = {module: deps for module, deps in transitive_graph.items() if '.' in module}
            if non_top_level_modules:
                most_deps_module = max(non_top_level_modules.items(), key=lambda x: len(x[1]))
                print(f"  Module with most dependencies: {most_deps_module[0]} ({len(most_deps_module[1])} deps)")

        # Only print transitive dependency top lists if not in quiet mode
        if not quiet_mode:
            # Always filter out top-level modules
            filtered_transitive_graph = {module: deps for module, deps in transitive_graph.items()
                                        if '.' in module}
            if filtered_transitive_graph:
                # Only print this if we've actually filtered out modules
                if len(transitive_graph) != len(filtered_transitive_graph):
                    print(f"Filtered out {len(transitive_graph) - len(filtered_transitive_graph)} top-level modules.")

                # Print top modules with most dependencies (transitive)
                print(f"\nTop {args.top_dependent} modules with most dependencies (including transitive):")
                sorted_modules = sorted(filtered_transitive_graph.items(), key=lambda x: len(x[1]), reverse=True)
                for i, (module, deps) in enumerate(sorted_modules[:args.top_dependent], 1):
                    print(f"  {i}. `{module}` {len(deps)} dependencies")
            else:
                print("\nNo non-top-level modules found for transitive analysis.")

    # Check for modules that depend on a specific module
    if args.find_dependents:
        if not transitive_graph:
            if not quiet_mode:
                print("Computing transitive closure of dependencies...")
            transitive_graph = compute_transitive_closure(graph)

        dependent_modules = find_dependent_modules(transitive_graph, args.find_dependents)

        print(f"\nModules that depend on '{args.find_dependents}':")
        print(f"Found {len(dependent_modules)} dependent modules")

        if dependent_modules:
            # Sort alphabetically for easier reading
            for module in sorted(dependent_modules):
                print(f"  {module}")

            # Optionally export to a file if requested
            if args.json:
                dependents_json = os.path.splitext(args.json)[0] + f"-dependents-of-{args.find_dependents.replace('.', '-')}.json"
                with open(dependents_json, 'w') as f:
                    json.dump(dependent_modules, f, indent=2)
                print(f"Dependent modules exported to {dependents_json}")
        else:
            print("  No modules depend on this module")

    # Only print remaining statistics if not in quiet mode
    if not quiet_mode:
        # Always filter out top-level modules for direct dependencies
        filtered_graph = {module: deps for module, deps in graph.items() if '.' in module}

        if filtered_graph:
            # Print modules with most direct dependencies
            direct_dep_count = {module: len(deps) for module, deps in filtered_graph.items()}
            print(f"\nTop {args.top_dependent} modules with most direct dependencies:")
            for i, (module, count) in enumerate(sorted(direct_dep_count.items(), key=lambda x: x[1], reverse=True)[:args.top_dependent], 1):
                print(f"  {i}. {module}: {count} direct dependencies")
        else:
            print("\nNo non-top-level modules found for direct dependency analysis.")

        if not any([args.dot, args.json, args.transitive, args.transitive_dot, args.transitive_json, args.find_dependents]):
            # Filter the imported modules count to only include non-top-level modules
            most_imported = defaultdict(int)
            for _, deps in graph.items():
                for dep in deps:
                    if '.' in dep:  # Only count imports of non-top-level modules
                        most_imported[dep] += 1

            if most_imported:
                print("\nTop 10 most imported non-top-level modules:")
                for module, count in sorted(most_imported.items(), key=lambda x: x[1], reverse=True)[:10]:
                    print(f"  `{module}` {count} imports")
            else:
                print("\nNo non-top-level modules found for import analysis.")

if __name__ == "__main__":
    main()

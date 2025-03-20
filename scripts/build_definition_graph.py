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

def extract_module_name(file_path, root_dir):
    """Extract the module name from a file path."""
    rel_path = os.path.relpath(file_path, root_dir)
    if rel_path.endswith('.lagda.md'):
        module_name = rel_path[:-9]
    else:  # .agda
        module_name = rel_path[:-5]
    module_name = module_name.replace('/', '.')
    return module_name

def extract_definitions(file_path):
    """
    Extract all definitions from a file.
    Returns a list of tuples (definition_name, line_number, line_content)
    """
    # Define a blacklist of regex patterns for definition names to exclude
    definition_blacklist_patterns = [
        r'^[a-zA-Z]$',  # Single letter names
        r'^l\d+$',      # 'l' followed by a number
    ]

    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Determine if this is a literate Agda file (.lagda.md)
    is_literate_agda = file_path.endswith('.lagda.md')

    # For literate Agda files, extract only content within code blocks
    if is_literate_agda:
        # Extract Agda code blocks (```agda ... ```)
        code_blocks = re.findall(r'```agda\n(.*?)```', content, re.DOTALL)
        # Combine all code blocks into a single string with line numbers preserved
        processed_lines = []
        line_num = 0
        for block in code_blocks:
            block_lines = block.split('\n')
            processed_lines.extend([(line_num + i, line) for i, line in enumerate(block_lines)])
            # Update line_num to account for the block and the delimiters
            line_num += len(block_lines) + 2  # +2 for ```agda and ```
    else:
        # For regular .agda files, process all lines
        lines = content.split('\n')
        processed_lines = [(i, line) for i, line in enumerate(lines)]

    # Look for lines of the form "identifier : type"
    pattern = r'^\s*([^\s;{}()@"]+)\s+:(?=$|\s)'

    # Add pattern for data and record definitions
    data_record_pattern = r'^\s*(data|record)\s*\n?\s+(\S+)(?:$|\!\}|[\s;{}()@"._])'

    definitions = []

    # Process regular definitions
    for line_num, line in processed_lines:
        match = re.search(pattern, line)
        if match:
            definition_name = match.group(1)
            # Skip if it's a comment line or matches a blacklist pattern
            if not line.strip().startswith('--') and not any(re.match(pattern, definition_name) for pattern in definition_blacklist_patterns):
                # Remove underscores from definition name
                definition_name = definition_name.replace('_', '')
                definitions.append((definition_name, line_num, line))

    # Process data and record definitions
    i = 0
    while i < len(processed_lines):
        line_num, line = processed_lines[i]

        # Check for data or record declarations that might span multiple lines
        if re.match(r'^\s*(data|record)\s*$', line):
            # If the keyword is alone on a line, check the next line
            if i + 1 < len(processed_lines):
                next_line_num, next_line = processed_lines[i+1]
                combined_line = line + ' ' + next_line
                match = re.search(data_record_pattern, combined_line)
                if match:
                    definition_name = match.group(2)
                    if not any(re.match(pattern, definition_name) for pattern in definition_blacklist_patterns):
                        definition_name = definition_name.replace('_', '')
                        definitions.append((definition_name, line_num, combined_line))
        else:
            # Check for data or record declarations on the same line
            match = re.search(data_record_pattern, line)
            if match:
                definition_name = match.group(2)
                if not line.strip().startswith('--') and not any(re.match(pattern, definition_name) for pattern in definition_blacklist_patterns):
                    definition_name = definition_name.replace('_', '')
                    definitions.append((definition_name, line_num, line))

        i += 1

    return definitions

def extract_definition_bodies(file_path, definitions):
    """
    Extract the body of each definition.
    Returns a dictionary mapping definition names to their bodies.
    """
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Determine if this is a literate Agda file (.lagda.md)
    is_literate_agda = file_path.endswith('.lagda.md')

    # Process content depending on file type
    if is_literate_agda:
        # Extract Agda code blocks
        code_blocks = re.findall(r'```agda\n(.*?)```', content, re.DOTALL)
        # Create a mapping from line numbers in original file to line content
        line_to_content = {}
        line_num = 0
        for block in code_blocks:
            block_lines = block.split('\n')
            for i, line in enumerate(block_lines):
                line_to_content[line_num + i] = line
            line_num += len(block_lines) + 2  # +2 for ```agda and ```

        # Create a list of (line_number, line) for all code blocks
        lines = []
        for i in sorted(line_to_content.keys()):
            lines.append((i, line_to_content[i]))
    else:
        # For regular .agda files, process all lines
        lines = [(i, line) for i, line in enumerate(content.split('\n'))]

    definition_bodies = {}

    for i, (definition_name, def_line_num, _) in enumerate(definitions):
        # Find the start of the body (the first top-level colon after the definition name)
        body_start = None

        # Find the line index in our processed lines list that corresponds to the definition line
        def_idx = None
        for idx, (line_num, _) in enumerate(lines):
            if line_num == def_line_num:
                def_idx = idx
                break

        if def_idx is None:
            continue  # Skip if we couldn't find the definition line

        # Look for the first top-level colon after the definition name
        current_idx = def_idx
        paren_level = 0  # Track the nesting level of parentheses

        while current_idx < len(lines) and body_start is None:
            line_num, line = lines[current_idx]

            # Process character by character to track parentheses nesting
            for char_idx, char in enumerate(line):
                if char == '(':
                    paren_level += 1
                elif char == ')':
                    paren_level = max(0, paren_level - 1)  # Ensure we don't go negative
                elif char == ':' and paren_level == 0:
                    # Found a top-level colon
                    body_start = (current_idx, char_idx + 1)  # Start after the colon
                    break

            current_idx += 1

        if body_start is None:
            continue  # No body found or constructor/postulate without implementation

        # Find the end of the body (the next definition or end of code block)
        body_end = None
        if i < len(definitions) - 1:
            next_def_idx = None
            for idx, (line_num, _) in enumerate(lines):
                if line_num == definitions[i + 1][1]:
                    next_def_idx = idx
                    break
            if next_def_idx is not None:
                body_end = (next_def_idx, 0)

        if body_end is None:
            body_end = (len(lines), 0)  # End of file

        # Extract the body
        body = ""
        if body_start[0] == body_end[0]:
            # Body is on the same line
            body = lines[body_start[0]][1][body_start[1]:body_end[1]]
        else:
            # Body spans multiple lines
            body = lines[body_start[0]][1][body_start[1]:]
            for j in range(body_start[0] + 1, body_end[0]):
                if j < len(lines):
                    body += '\n' + lines[j][1]
            if body_end[1] > 0 and body_end[0] < len(lines):
                body += '\n' + lines[body_end[0]][1][:body_end[1]]

        definition_bodies[definition_name] = body

    return definition_bodies

def build_definition_graph(root_dir):
    """
    Build a dependency graph of definitions from all Git-tracked Agda files.
    """
    agda_files = find_agda_files(root_dir)

    # Dictionary to store all definitions across all files
    all_definitions = {}  # Maps definition_name -> (module_name, file_path)
    module_definitions = defaultdict(list)  # Maps module_name -> list of def_names
    all_definition_bodies = {}  # Maps definition_name -> body

    print(f"Processing {len(agda_files)} Agda files...")

    # First pass: collect all definitions
    for file_path in agda_files:
        try:
            module_name = extract_module_name(file_path, root_dir)
            definitions = extract_definitions(file_path)

            for def_name, _, _ in definitions:
                # Store with module name to avoid name collisions across modules
                qualified_name = f"{module_name}.{def_name}"
                all_definitions[qualified_name] = (module_name, file_path)
                module_definitions[module_name].append(def_name)
        except Exception as e:
            print(f"Error processing definitions in {file_path}: {e}")

    print(f"Found {len(all_definitions)} unique qualified definitions")

    # Second pass: extract bodies and build the dependency graph
    for file_path in agda_files:
        try:
            module_name = extract_module_name(file_path, root_dir)
            definitions = extract_definitions(file_path)
            definition_bodies = extract_definition_bodies(file_path, definitions)

            for def_name, body in definition_bodies.items():
                qualified_name = f"{module_name}.{def_name}"
                all_definition_bodies[qualified_name] = body
        except Exception as e:
            print(f"Error processing definition bodies in {file_path}: {e}")

    # Build the dependency graph
    graph = defaultdict(list)

    # Create a reverse lookup from bare definition name to qualified names
    # This will help us find all possible qualified definitions for a given bare name
    bare_to_qualified = defaultdict(list)
    for qualified_name in all_definitions:
        bare_name = qualified_name.split('.')[-1]
        bare_to_qualified[bare_name].append(qualified_name)

    # Define a blacklist of regex patterns to ignore when finding dependencies
    token_blacklist_patterns = [
        r'^[a-zA-Z]$',  # Single letter names
        r'^l\d+$',      # 'l' followed by a number
    ]

    # For each definition body, check if it contains references to other definitions
    for def_name, body in all_definition_bodies.items():
        module_name = def_name.rsplit('.', 1)[0]  # Extract module name from qualified definition name
        bare_def_name = def_name.split('.')[-1]   # Extract the bare definition name

        # Split the body into tokens (only identifiers, not qualified)

        # The regex uses lookbehind and lookahead to match identifiers surrounded by separators
        # but only captures the identifier itself
        tokens = []
        pattern = r"""(?:^|\{\!|\{-\#|[\s;{}()@"._])(?!'|--)([^\s;{}()@"._]+)(?:$|\!\}|[\s;{}()@"._])"""
        matches = re.finditer(pattern, ' ' + body + ' ')  # Add spaces to ensure boundary matching
        for match in matches:
            tokens.append(match.group(1))

        # Track unique dependencies to avoid duplicates
        unique_deps = set()

        # Check if any token matches a known definition name (ignore qualified parts)
        for token in tokens:
            # Remove underscores from the token for matching
            clean_token = token.replace('_', '')

            # Skip tokens that are the definition itself
            if clean_token == bare_def_name:
                continue

            # Skip tokens that match any regex in the blacklist
            if any(re.match(pattern, clean_token) for pattern in token_blacklist_patterns):
                continue

            # Check if it's a reference to a definition in the same module first
            if clean_token in module_definitions[module_name]:
                qualified_token = f"{module_name}.{clean_token}"
                unique_deps.add(qualified_token)
            # Otherwise, it might be a reference to an imported definition
            # For now, we'll just consider all possible matches to be conservative
            elif clean_token in bare_to_qualified and len(bare_to_qualified[clean_token]) > 0:
                # Add potential dependencies
                # For simplicity and to avoid false positives with common names,
                # we'll only consider it a dependency if there's exactly one definition with this name
                if len(bare_to_qualified[clean_token]) == 1:
                    unique_deps.add(bare_to_qualified[clean_token][0])

        # Add all unique dependencies to the graph
        graph[def_name] = list(unique_deps)

    return graph, all_definitions

def compute_transitive_closure(graph):
    """
    Compute the transitive closure of the dependency graph.
    Returns a new graph where each definition has a list of all its
    direct and indirect dependencies.
    """
    transitive_closure = defaultdict(set)

    # For each definition, perform BFS to find all dependencies
    for definition in graph:
        queue = deque(graph[definition])
        visited = set(graph[definition])

        while queue:
            dep = queue.popleft()
            transitive_closure[definition].add(dep)

            # Add any dependencies of this dependency that we haven't seen yet
            for next_dep in graph.get(dep, []):
                if next_dep not in visited:
                    visited.add(next_dep)
                    queue.append(next_dep)

    # Convert sets back to lists for consistent output
    return {definition: list(deps) for definition, deps in transitive_closure.items()}

def export_to_dot(graph, output_file):
    """Export the graph to DOT format for visualization with Graphviz."""
    with open(output_file, 'w') as f:
        f.write('digraph Dependencies {\n')
        f.write('  node [shape=box];\n')

        for definition, deps in graph.items():
            for dep in deps:
                f.write(f'  "{definition}" -> "{dep}";\n')

        f.write('}\n')

def export_to_json(graph, output_file):
    """Export the graph to JSON format."""
    with open(output_file, 'w') as f:
        json.dump(graph, f, indent=2)

def find_dependent_definitions(graph, target_definition):
    """
    Find all definitions that depend on the target definition.

    If the target_definition is not fully qualified, it will match any definition
    that ends with this name (i.e., any module's definition with this bare name).
    """
    dependent_definitions = []

    # Check if the target is a fully qualified name or just a bare name
    is_qualified = '.' in target_definition

    for definition, dependencies in graph.items():
        if is_qualified:
            # Direct match for fully qualified names
            if target_definition in dependencies:
                dependent_definitions.append(definition)
        else:
            # For bare names, check if any dependency ends with the target
            for dep in dependencies:
                if dep.endswith('.' + target_definition):
                    dependent_definitions.append(definition)
                    break

    return dependent_definitions

def find_module_dependent_definitions(graph, all_definitions, module_name):
    """
    Find all definitions that transitively depend on any definition in the specified module.

    Args:
        graph: The dependency graph
        all_definitions: Dictionary mapping qualified definition names to (module_name, file_path)
        module_name: The name of the module to find dependents of

    Returns:
        A list of definition names that depend on any definition in the module
    """
    # Find all definitions in the target module
    module_definitions = []
    for qualified_name, (def_module, _) in all_definitions.items():
        if def_module == module_name:
            module_definitions.append(qualified_name)

    if not module_definitions:
        return []

    # Find all definitions that depend on any definition in the module
    dependent_definitions = set()
    for definition in module_definitions:
        dependents = find_dependent_definitions(graph, definition)
        dependent_definitions.update(dependents)

    return list(dependent_definitions)

def find_module_direct_dependencies(graph, all_definitions, module_name):
    """
    Find all modules that directly depend on any definition in the specified module.

    Args:
        graph: The dependency graph
        all_definitions: Dictionary mapping qualified definition names to (module_name, file_path)
        module_name: The name of the module to find direct dependents of

    Returns:
        A list of module names that directly depend on any definition in the specified module
    """
    # Find all definitions in the target module
    module_definitions = []
    for qualified_name, (def_module, _) in all_definitions.items():
        if def_module == module_name:
            module_definitions.append(qualified_name)

    if not module_definitions:
        return []

    # Find all definitions that depend on any definition in the module
    dependent_modules = set()
    for source_def, dependencies in graph.items():
        source_module = source_def.rsplit('.', 1)[0]  # Extract module name from qualified definition name

        # Skip if the source is the same module we're checking dependencies for
        if source_module == module_name:
            continue

        # Check if this definition depends on any definition from our target module
        for dep in dependencies:
            if any(dep == target_def for target_def in module_definitions):
                dependent_modules.add(source_module)
                break

    return list(dependent_modules)

def main():
    parser = argparse.ArgumentParser(description='Build dependency graph of Agda definitions')
    parser.add_argument('root_dir', help='Root directory of the Agda library')
    parser.add_argument('--dot', help='Output file for DOT graph')
    parser.add_argument('--json', help='Output file for JSON representation')
    parser.add_argument('--transitive', action='store_true',
                        help='Compute transitive closure of dependencies')
    parser.add_argument('--transitive-dot', help='Output file for transitive closure DOT graph')
    parser.add_argument('--transitive-json', help='Output file for transitive closure JSON')
    parser.add_argument('--top-dependent', type=int, default=10,
                        help='Print top N definitions with most dependencies (default: 10)')
    parser.add_argument('--find-dependents', metavar='DEFINITION',
                        help='Find all definitions that depend on the specified definition')
    parser.add_argument('--find-module-dependents', metavar='MODULE',
                        help='Find all definitions that depend on any definition in the specified module')
    parser.add_argument('--find-module-deps', metavar='MODULE',
                        help='Find all modules that directly depend on any definition in the specified module')
    parser.add_argument('--quiet', action='store_true',
                        help='Suppress informational output, only show requested results')
    args = parser.parse_args()

    # If find_dependents, find_module_dependents, or find_module_deps is used, enable quiet mode by default
    quiet_mode = args.quiet or ((args.find_dependents or args.find_module_dependents or args.find_module_deps) and
                               not any([args.transitive, args.dot, args.json, args.transitive_dot, args.transitive_json]))

    if not quiet_mode:
        print(f"Analyzing Git-tracked Agda files in {args.root_dir}...")

    try:
        graph, all_definitions = build_definition_graph(args.root_dir)
    except Exception as e:
        print(f"Error building definition graph: {e}")
        return

    # No need for duplicate filtering as we're being more careful above
    # Just keep the graph as is

    if not quiet_mode:
        print(f"Found {len(graph)} tracked definitions with dependencies.")
        total_deps = sum(len(deps) for deps in graph.values())
        print(f"Total dependencies: {total_deps}")

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
    if args.transitive or args.transitive_dot or args.transitive_json or args.find_dependents or args.find_module_dependents:
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
            print(f"  Average dependencies per definition: {avg_deps:.2f}")
            print(f"  Maximum dependencies for a definition: {max_deps}")

    # Check for definitions that depend on a specific definition
    if args.find_dependents:
        if not transitive_graph:
            if not quiet_mode:
                print("Computing transitive closure of dependencies...")
            transitive_graph = compute_transitive_closure(graph)

        dependent_definitions = find_dependent_definitions(transitive_graph, args.find_dependents)

        # If no results with the input as provided, check if we need to look for it as a bare name
        if not dependent_definitions and '.' not in args.find_dependents:
            # Print possible fully qualified names that match this bare name
            matching_qualified_names = []
            for qualified_name in all_definitions:
                if qualified_name.endswith('.' + args.find_dependents):
                    matching_qualified_names.append(qualified_name)

            if matching_qualified_names:
                print(f"\nFound {len(matching_qualified_names)} definitions named '{args.find_dependents}':")
                for name in sorted(matching_qualified_names):
                    print(f"  {name}")
                print(f"\nTry searching with a fully qualified name like '--find-dependents {matching_qualified_names[0]}'")

        print(f"\nDefinitions that depend on '{args.find_dependents}':")
        print(f"Found {len(dependent_definitions)} dependent definitions")

        if dependent_definitions:
            # Sort alphabetically for easier reading
            for definition in sorted(dependent_definitions):
                print(f"  {definition}")

            # Optionally export to a file if requested
            if args.json:
                dependents_json = os.path.splitext(args.json)[0] + f"-dependents-of-{args.find_dependents.replace('.', '-')}.json"
                with open(dependents_json, 'w') as f:
                    json.dump(dependent_definitions, f, indent=2)
                print(f"Dependent definitions exported to {dependents_json}")
        else:
            print("  No definitions depend on this definition")

    # Check for definitions that depend on any definition in a module
    if args.find_module_dependents:
        if not transitive_graph:
            if not quiet_mode:
                print("Computing transitive closure of dependencies...")
            transitive_graph = compute_transitive_closure(graph)

        module_dependent_definitions = find_module_dependent_definitions(transitive_graph, all_definitions, args.find_module_dependents)

        print(f"\nDefinitions that depend on module '{args.find_module_dependents}':")
        print(f"Found {len(module_dependent_definitions)} dependent definitions")

        if module_dependent_definitions:
            # Sort alphabetically for easier reading
            for definition in sorted(module_dependent_definitions):
                print(f"  {definition}")

            # Optionally export to a file if requested
            if args.json:
                module_dependents_json = os.path.splitext(args.json)[0] + f"-dependents-of-module-{args.find_module_dependents.replace('.', '-')}.json"
                with open(module_dependents_json, 'w') as f:
                    json.dump(module_dependent_definitions, f, indent=2)
                print(f"Module dependent definitions exported to {module_dependents_json}")
        else:
            print(f"  No definitions depend on any definition in module '{args.find_module_dependents}'")

    # Check for modules that directly depend on a module
    if args.find_module_deps:
        module_dependencies = find_module_direct_dependencies(graph, all_definitions, args.find_module_deps)

        print(f"\nModules that directly depend on module '{args.find_module_deps}':")
        print(f"Found {len(module_dependencies)} dependent modules")

        if module_dependencies:
            # Sort alphabetically for easier reading
            for module in sorted(module_dependencies):
                print(f"  {module}")

            # Optionally export to a file if requested
            if args.json:
                module_deps_json = os.path.splitext(args.json)[0] + f"-modules-depend-on-{args.find_module_deps.replace('.', '-')}.json"
                with open(module_deps_json, 'w') as f:
                    json.dump(module_dependencies, f, indent=2)
                print(f"Module dependencies exported to {module_deps_json}")
        else:
            print(f"  No modules directly depend on module '{args.find_module_deps}'")

    # Only print remaining statistics if not in quiet mode
    if not quiet_mode:
        # Print top definitions with most direct dependencies
        direct_dep_count = {definition: len(deps) for definition, deps in graph.items()}

        if direct_dep_count:
            print(f"\nTop {args.top_dependent} definitions with most direct dependencies:")
            for i, (definition, count) in enumerate(sorted(direct_dep_count.items(), key=lambda x: x[1], reverse=True)[:args.top_dependent], 1):
                print(f"  {i}. {definition}: {count} direct dependencies")
        else:
            print("\nNo definitions found for direct dependency analysis.")

        if not any([args.dot, args.json, args.transitive, args.transitive_dot, args.transitive_json, args.find_dependents]):
            # Calculate the most depended upon definitions
            most_depended = defaultdict(int)
            for _, deps in graph.items():
                for dep in deps:
                    most_depended[dep] += 1

            if most_depended:
                print("\nTop 10 most used definitions:")
                for definition, count in sorted(most_depended.items(), key=lambda x: x[1], reverse=True)[:10]:
                    print(f"  {definition}: {count} usages")
            else:
                print("\nNo definitions found for usage analysis.")

if __name__ == "__main__":
    main()

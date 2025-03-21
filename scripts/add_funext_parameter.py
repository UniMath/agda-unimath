#!/usr/bin/env python3

import os
import re
import argparse
from pathlib import Path
import shutil
import sys

# Import the dependency graph functionality
from build_dependency_graph import compute_transitive_closure, build_dependency_graph

FUNEXT_MODULE = "foundation.function-extensionality"
FUNEXT_IMPORT = "open import foundation.function-extensionality-axiom"
FUNEXT_PARAM = "(funext : function-extensionality)"

def find_module_declaration(content):
    """Find the main module declaration in a file."""
    # Match 'module name.of.module' potentially with parameters
    module_pattern = r'^module\s+([^\s\(]+)(?:\s+[^\n]*)?(?:\n|$)'
    match = re.search(module_pattern, content, re.MULTILINE)
    if match:
        return match.group(0), match.group(1)
    return None, None

def modify_file_content(file_path, module_name, dependent_modules):
    """
    Modify the content of an Agda file to:
    1. Remove any existing function extensionality imports
    2. Add function extensionality import right before module declaration
    3. Add funext parameter to module declaration
    4. Add funext parameter to dependent imports
    """
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Find module declaration
    module_decl, module_id = find_module_declaration(content)
    if not module_decl:
        print(f"Warning: Could not find module declaration in {file_path}")
        return None

    # Remove any existing function extensionality imports
    modified_content = content
    existing_import_pattern = rf'{re.escape(FUNEXT_IMPORT)}(?:\s*\n|\n)'
    modified_content = re.sub(existing_import_pattern, '', modified_content)

    # If content changed, get updated module declaration
    if modified_content != content:
        print(f"Note: Removed existing function extensionality import in {file_path}")
        module_decl, module_id = find_module_declaration(modified_content)
        content = modified_content

    # Check if the module declaration already has funext parameter
    has_funext_param = "funext" in module_decl

    # Add function extensionality import and update module declaration
    lines = content.split('\n')
    updated_lines = []
    module_line_found = False

    for line in lines:
        # When we find the module declaration line
        if not module_line_found and line.startswith('module '):
            # Add the import before the module declaration
            updated_lines.append(FUNEXT_IMPORT + '\n')
            module_line_found = True

            # Add funext parameter to module declaration if needed
            if not has_funext_param:
                if "where" in line:
                    # If there's a 'where' clause, put parameters before it
                    updated_line = re.sub(r'(\s+where)', f" {FUNEXT_PARAM}\\1", line)
                else:
                    # Otherwise, add at the end
                    updated_line = line.rstrip() + f" {FUNEXT_PARAM} where"
                updated_lines.append(updated_line)
            else:
                updated_lines.append(line)
        else:
            updated_lines.append(line)

    modified_content = '\n'.join(updated_lines)

    # Modify imports of modules that depend on funext
    for dep_module in dependent_modules:
        # Find imports of this module
        import_pattern = rf'open\s+import\s+{re.escape(dep_module)}(?:\s+[^\n]*)?(?:\n|$)'
        for match in re.finditer(import_pattern, modified_content):
            import_stmt = match.group(0)
            # Skip if already has funext
            if "funext" in import_stmt:
                continue

            # Add funext parameter to the import
            if import_stmt.strip().endswith(dep_module):
                # No existing parameters
                new_import = import_stmt.rstrip() + " funext\n"
            else:
                # Has other parameters, add funext
                new_import = import_stmt.replace(dep_module, f"{dep_module} funext")

            modified_content = modified_content[:match.start()] + new_import + modified_content[match.end():]

    # Additionally, handle direct imports of foundation.function-extensionality
    # Make sure we only match the exact module name, not ones that start with it
    funext_direct_import_pattern = r'open\s+import\s+foundation\.function-extensionality\b(?!-axiom)'

    # Use finditer with the MULTILINE flag to ensure we catch all instances
    for match in re.finditer(funext_direct_import_pattern, modified_content, re.MULTILINE):
        import_stmt = match.group(0)
        # Skip if already has funext
        if "funext" in import_stmt:
            continue

        # Add funext parameter to the import
        if import_stmt.strip().endswith("foundation.function-extensionality"):
            # No existing parameters
            new_import = import_stmt.rstrip() + " funext\n"
        else:
            # Has other parameters, add funext appropriately
            # Use a more specific pattern to ensure we only replace the exact module name
            new_import = re.sub(r'(foundation\.function-extensionality)\b(?!-axiom)', r'\1 funext', import_stmt)

        modified_content = modified_content[:match.start()] + new_import + modified_content[match.end():]

    # Only return modified content if changes were made
    if modified_content != content:
        return modified_content
    else:
        print(f"No changes needed for {file_path}")
        return None

def main():
    parser = argparse.ArgumentParser(description='Add function extensionality parameter to Agda modules')
    parser.add_argument('root_dir', help='Root directory of the Agda library')
    parser.add_argument('--dry-run', action='store_true',
                        help='Show what would be changed without making actual changes')
    parser.add_argument('--backup', action='store_true',
                        help='Create backup files before modifying')
    args = parser.parse_args()

    root_dir = args.root_dir

    print(f"Building dependency graph for {root_dir}...")
    graph, module_to_file = build_dependency_graph(root_dir)

    print("Computing transitive closure of dependencies...")
    transitive_graph = compute_transitive_closure(graph)

    # Find all modules that depend on foundation.function-extensionality
    funext_dependent_modules = []
    for module, deps in transitive_graph.items():
        if FUNEXT_MODULE in deps:
            funext_dependent_modules.append(module)

    print(f"Found {len(funext_dependent_modules)} modules that depend on {FUNEXT_MODULE}")

    # Create a mapping of each file to its dependent modules
    file_dependent_modules = {}
    for module in funext_dependent_modules:
        if module in module_to_file:
            file_path = module_to_file[module]
            file_dependent_modules[file_path] = [
                dep for dep in graph.get(module, [])
                if dep in funext_dependent_modules
            ]

    # Process each file
    modified_count = 0
    for file_path, dependent_modules in file_dependent_modules.items():
        module_name = next((m for m, f in module_to_file.items() if f == file_path), None)
        if not module_name:
            continue

        print(f"Processing {module_name} ({file_path})...")
        modified_content = modify_file_content(file_path, module_name, dependent_modules)

        if modified_content:
            if args.dry_run:
                print(f"Would modify: {file_path}")
            else:
                if args.backup:
                    backup_path = f"{file_path}.bak"
                    shutil.copy2(file_path, backup_path)
                    print(f"Created backup: {backup_path}")

                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(modified_content)
                print(f"Modified: {file_path}")
                modified_count += 1

    if args.dry_run:
        print(f"\nDry run completed. {modified_count} files would be modified.")
    else:
        print(f"\nCompleted. Modified {modified_count} files.")

if __name__ == "__main__":
    main()

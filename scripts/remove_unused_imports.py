#!/usr/bin/env python3
# Run this script:
# $ ./scripts/remove_unused_imports.py [optional: path_to_file_or_folder ...]

import os
import sys
import pathlib
import shutil
import utils
import utils.multithread
from concurrent.futures import ThreadPoolExecutor
from fix_imports import *


def process_agda_file(agda_file, agda_options, root, temp_dir):

    # Read file
    with open(agda_file, 'r', encoding='UTF-8') as file:
        content = file.read()

    # Categorize all imports
    block, start, end = get_imports_block(content)
    public, nonpublic, open_statements = categorize_imports(block)
    agda_module = utils.get_agda_module_name(agda_file, root)

    # If no nonpublic imports, skip
    if nonpublic is None:
        utils.multithread.thread_safe_print(
            f"'{agda_module}' Could not find imports.")
        return
    elif len(nonpublic) == 0:
        utils.multithread.thread_safe_print(
            f"'{agda_module}' No nonpublic imports.")
        return

    # Proceed with search for unused imports
    temp_root = os.path.join(root, temp_dir)
    temp_file = agda_file.replace(root, temp_root)
    temp_content = content.replace(
        f'\nmodule {agda_module}', f'\nmodule {temp_dir}.{agda_module}')
    temp_start = start + len(temp_dir) + 1
    temp_end = end + len(temp_dir) + 1
    os.makedirs(os.path.dirname(temp_file), exist_ok=True)

    # For each nonpublic import statement, test if the code compiles without the statement
    new_nonpublic = set(nonpublic)
    modified = False

    for import_statement in nonpublic:
        new_nonpublic.discard(import_statement)
        pretty_imports_block = prettify_imports_to_block(
            public, new_nonpublic, open_statements)
        new_temp_content = temp_content[:temp_start] + \
            pretty_imports_block + temp_content[temp_end:]
        with open(temp_file, 'w') as file:
            file.write(new_temp_content)

        if (utils.call_agda(agda_options, temp_file) != 0):
            new_nonpublic.add(import_statement)
        else:
            modified = True

    # This file will always exist, as we have already checked if nonpublic has length 0
    if os.path.isfile(temp_file):
        os.remove(temp_file)

    # Write final version if modified
    if modified:
        pretty_imports_block = prettify_imports_to_block(
            public, new_nonpublic, open_statements)
        new_content = content[:start] + pretty_imports_block + content[end:]

        with open(agda_file, 'w') as file:
            file.write(new_content)

        removed_imports = sorted(map(lambda s: s[len('open import '):], set(
            nonpublic).difference(new_nonpublic)))

        if utils.call_agda(agda_options, agda_file) != 0:
            # Something is wrong. Revert
            with open(agda_file, 'w') as file:
                file.write(content)

            utils.multithread.thread_safe_print(
                f"'{agda_module}' ERROR! The temporary file '{temp_file} typechecked with imports {removed_imports} removed, but not the actual file '{agda_file}'. Please report this.")
            return

        utils.multithread.thread_safe_print(
            f"'{agda_module}' had {len(removed_imports)} unused imports: {removed_imports}")
    else:
        utils.multithread.thread_safe_print(
            f"'{agda_module}' No unused imports.")


def get_agda_files(path):
    if os.path.isfile(path):
        return [path] if utils.is_agda_file(pathlib.Path(path)) else []
    elif os.path.isdir(path):
        def filter_agda_files(f): return utils.is_agda_file(
            pathlib.Path(f)) and os.path.dirname(f) != path
        return list(filter(filter_agda_files, utils.get_files_recursive(path)))
    else:
        utils.multithread.thread_safe_print(
            f"Warning: '{path}' is not a valid file or directory. Skipping.")
        return []


if __name__ == '__main__':
    root = 'src'
    if len(sys.argv) > 1:
        input_paths = sys.argv[1:]
        # root = os.path.commonpath(input_paths)  # Find common root for all inputs
    else:
        # Default behavior when no argument is provided
        root = 'src'
        input_paths = [root]

    temp_dir = 'temp'
    status = 0
    agda_options = '--without-K --exact-split --no-import-sorts --auto-inline --no-caching'

    temp_root = os.path.join(root, temp_dir)
    shutil.rmtree(temp_root, ignore_errors=True)

    # Get Agda files based on the inputs
    agda_files = []
    for path in input_paths:
        agda_files.extend(get_agda_files(path))

    if not agda_files:
        utils.multithread.thread_safe_print(
            'No Agda files found in the specified paths.')
        sys.exit(1)

    # Sort the files by Git modification status and last commit date
    def sort_key(file):
        return (-int(utils.is_file_modified(file)), -utils.get_git_last_modified(file))

    sorted_agda_files = sorted(agda_files, key=sort_key)

    with ThreadPoolExecutor() as executor:
        executor.map(lambda file: process_agda_file(
            file, agda_options, root, temp_dir), sorted_agda_files)

    # shutil.rmtree(temp_root)
    sys.exit(status)

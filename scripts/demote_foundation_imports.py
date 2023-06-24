#!/usr/bin/env python3
# Run this script:
# $ ./scripts/demote_foundation_imports.py

import itertools
import os
import shutil
import utils
import utils.multithread
from concurrent.futures import ThreadPoolExecutor
from fix_imports import *


def process_agda_file(agda_file, agda_options, root, temp_dir):

    with open(agda_file, 'r', encoding='UTF-8') as file:
        content = file.read()
    block, start, end = get_imports_block(content)
    public, nonpublic, open_statements = categorize_imports(block)
    agda_module = utils.get_agda_module_name(agda_file, root)

    if nonpublic is None:
        utils.multithread.thread_safe_print(
            f"'{agda_module}' Could not find imports.")
        return

        # Subdivide imports into namespaces
    namespaces = subdivide_namespaces_imports(nonpublic)

    if not 'foundation' in namespaces.keys():
        utils.multithread.thread_safe_print(
            f"'{agda_module}' has no foundation imports.")
        return

    new_nonpublic = set(nonpublic)

    # Fast-track foundation files without definitions
    fast_track_modules = set()
    for module in namespaces['foundation']:
        if module in foundation_modules_without_definitions:
            import_statement = 'open import ' + module
            new_nonpublic.discard(import_statement)
            new_nonpublic.add(import_statement.replace(
                'foundation.', 'foundation-core.'))
            pretty_imports_block = prettify_imports_to_block(
                public, new_nonpublic, open_statements)
            fast_track_modules.add(module)

    modified = len(fast_track_modules) > 0

    namespaces['foundation'] = namespaces['foundation'].difference(
        fast_track_modules)

    # Proceed with search

    temp_root = os.path.join(root, temp_dir)
    temp_file = agda_file.replace(root, temp_root)
    temp_content = content.replace(
        f'\nmodule {agda_module}', f'\nmodule {temp_dir}.{agda_module}')
    temp_start = start + len(temp_dir) + 1
    temp_end = end + len(temp_dir) + 1
    os.makedirs(os.path.dirname(temp_file), exist_ok=True)

    for module in namespaces['foundation']:
        if module[len('foundation.'):] not in core_submodules:
            continue

        import_statement = 'open import ' + module
        new_nonpublic.discard(import_statement)
        new_nonpublic.add(import_statement.replace(
            'foundation.', 'foundation-core.'))

        pretty_imports_block = prettify_imports_to_block(
            public, new_nonpublic, open_statements)

        new_temp_content = temp_content[:temp_start] + \
            pretty_imports_block + \
            temp_content[temp_end:]

        with open(temp_file, 'w') as file:
            file.write(new_temp_content)

        if (utils.call_agda(agda_options, temp_file) != 0):
            new_nonpublic.discard(import_statement.replace(
                'foundation.', 'foundation-core.'))
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
                f"'{agda_module}' ERROR! The temporary file '{temp_file} typechecked with imports {removed_imports} removed, but not the actual file '{agda_file}'. Please report this.", file=sys.stderr)
            return

        utils.multithread.thread_safe_print(
            f"'{agda_module}' had {len(removed_imports)} unused imports: {removed_imports}")
    else:
        utils.multithread.thread_safe_print(
            f"'{agda_module}' No unused imports.")


if __name__ == '__main__':
    # foundation to foundation-core import demoter

    # Checks every foundation and foundation-core file, for every import statement from foundation, if that file still typechecks of the import statement is replaced by importing from core. If so, keeps the change.

    # Note: Only demotes imports in foundation and foundation-core modules

    root = 'src'
    temp_dir = 'temp'
    status = 0
    agda_options = '--without-K --exact-split --no-import-sorts --auto-inline --no-caching'

    temp_root = os.path.join(root, temp_dir)
    shutil.rmtree(temp_root, ignore_errors=True)

    core_filenames = sorted(filter(lambda f: f.endswith(
        '.lagda.md'), os.listdir('src/foundation-core')))
    foundation_filenames = sorted(
        filter(lambda f: f.endswith('.lagda.md'), os.listdir('src/foundation')))
    foundation_filepaths = map(lambda f: os.path.join(
        root, 'foundation', f), foundation_filenames)
    core_filepaths = map(lambda f: os.path.join(
        root, 'foundation-core', f), core_filenames)
    foundation_and_core_files = tuple(
        itertools.chain(foundation_filepaths, core_filepaths))

    core_submodules = set(
        map(lambda f: f[:f.rfind('.lagda.md')], core_filenames))

    foundation_files_without_definitions = filter(lambda f: utils.has_no_definitions(os.path.join(
        root, 'foundation', f)) and f[:f.rfind('.lagda.md')] in core_submodules, foundation_filenames)
    foundation_modules_without_definitions = set(map(
        lambda f: 'foundation.' + f[:f.rfind('.lagda.md')], foundation_files_without_definitions))

    print('The following module imports can be fast-tracked, as they do not have any definitions:')
    print(*map(lambda m: ' - ' + m,
          sorted(foundation_modules_without_definitions)), sep='\n')
    print()

    with ThreadPoolExecutor() as executor:
        executor.map(lambda file: process_agda_file(
            file, agda_options, root, temp_dir), foundation_and_core_files)

    shutil.rmtree(temp_root)
    sys.exit(status)

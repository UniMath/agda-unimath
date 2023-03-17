from fix_imports import *
import os
import pathlib
import shutil
import utils
from concurrent.futures import ThreadPoolExecutor


def process_agda_file(agda_file, agda_options, root, temp_dir):

    def get_agda_module_name(file_path):
        return file_path[len(root) + 1:file_path.rfind('.lagda.md')].replace('/', '.').replace('\\', '.')

    # Read file
    with open(agda_file, 'r', encoding='UTF-8') as file:
        content = file.read()

    # Categorize all imports
    block, start, end = get_imports_block(content)
    public, nonpublic, open_statements = categorize_imports(block)
    agda_module = get_agda_module_name(agda_file)

    # If no nonpublic imports, skip
    if not nonpublic:
        print(f"'{agda_module}' Could not find imports. Skipping.")
        return

    # # We can assume the file would compile, as this is usually the case.
    # # Otherwise, no harm is done, it will just determine that the file does
    # # not compile with any of the imports removed either, so the result is the same
    # # If file doesn't compile, skip
    # elif (utils.call_agda(agda_options, agda_file) != 0):
    #     print(f"'{agda_file}': ERROR! did not typecheck. Skipping.")
    #     return

    # Proceed with search for unused imports
    temp_root = os.path.join(root, temp_dir)
    temp_file = agda_file.replace(root, temp_root)
    new_nonpublic = set(nonpublic)

    # For each nonpublic import statement, test if the code compiles without the statement
    modified = False
    os.makedirs(os.path.dirname(temp_file), exist_ok=True)
    temp_content = content.replace(
        f"\nmodule {agda_module}", f"\nmodule {temp_dir}.{agda_module}")
    temp_start = start + len(temp_dir) + 1
    temp_end = end + len(temp_dir) + 1

    for statement in nonpublic:
        new_nonpublic.discard(statement)
        pretty_imports_block = prettify_imports_to_block(
            public, new_nonpublic, open_statements)
        new_temp_content = temp_content[:temp_start] + \
            pretty_imports_block + temp_content[temp_end:]
        with open(temp_file, 'w') as file:
            file.write(new_temp_content)

        if (utils.call_agda(agda_options, temp_file) != 0):
            new_nonpublic.add(statement)
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

        removed_imports = sorted(map(lambda s: s[len("open import "):], set(
            nonpublic).difference(new_nonpublic)))

        if utils.call_agda(agda_options, agda_file) != 0:
            # Something is wrong. Revert
            with open(agda_file, 'w') as file:
                file.write(content)

            print(f"'{agda_module}' ERROR! The temporary file '{temp_file} typechecked with imports {removed_imports} removed, but not the actual file '{agda_file}'. Please report this.")
            return

        print(
            f"'{agda_module}' had {len(removed_imports)} unused imports: {removed_imports}")
    else:
        print(f"'{agda_module}' No unused imports.")


if __name__ == "__main__":
    root = "src"
    temp_dir = "temp"
    status = 0
    agda_options = "--without-K --exact-split"

    temp_root = os.path.join(root, temp_dir)
    shutil.rmtree(temp_root, ignore_errors=True)

    def filter_agda_files(f): return utils.is_agda_file(
        pathlib.Path(f)) and os.path.dirname(f) != root

    agda_files = sorted(
        filter(filter_agda_files, utils.get_files_recursively(root)))

    with ThreadPoolExecutor() as executor:
        executor.map(lambda file: process_agda_file(
            file, agda_options, root, temp_dir), agda_files)

    shutil.rmtree(temp_root)
    sys.exit(status)

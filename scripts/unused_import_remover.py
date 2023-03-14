from fix_imports import *
import os
import pathlib
import utils

if __name__ == "__main__":
    # Import remover

    # Checks every file, import statement by import statement, if they still typecheck if the statement is removed. If so, removes that statemet.

    # CAUTION! If the script is interrupted while running, you will likely end up with a missing import statement in the last inspected file.

    root = "src"
    status = 0
    agda_options = "--without-K --exact-split"

    def filter_agda_files(f): return utils.is_agda_file(
        pathlib.Path(f)) and os.path.dirname(f) != root
    agda_files = sorted(
        filter(filter_agda_files, utils.get_files_recursively(root)))

    for i, agda_file in enumerate(agda_files):
        i_string = str(i+1).rjust(len(str(len(agda_files))))

        print(f"{i_string} of {len(agda_files)}: '{agda_file}'", end="")

        # Read file
        with open(agda_file, 'r', encoding='UTF-8') as file:
            contents = file.read()

        # Categorize all imports
        block, start, end = get_imports_block(contents)
        public, nonpublic, open_statements = categorize_imports(block)

        # If no nonpublic imports, skip
        if nonpublic is None or len(nonpublic) == 0:
            print(f" Could not find imports. Skipping.")
            continue
        # If file doesn't compile, skip
        elif (utils.call_agda(agda_options, agda_file) != 0):
            print(f" ERROR! did not typecheck. Skipping.")
            continue
        else:
            print(" typechecked.")

        new_nonpublic = set(nonpublic)

        # For each nonpublic import statement, test if the code compiles without the statement
        for statement in nonpublic:
            new_nonpublic.discard(statement)
            pretty_imports_block = prettify_imports_to_block(
                public, new_nonpublic, open_statements)

            new_content = contents[:start] + \
                pretty_imports_block + \
                contents[end:]

            with open(agda_file, 'w') as file:
                file.write(new_content)

            if (utils.call_agda(agda_options, agda_file) != 0):
                new_nonpublic.add(statement)
            else:
                print(f"    '{statement}' was unused")

        # Write final version
        pretty_imports_block = prettify_imports_to_block(
            public, new_nonpublic, open_statements)

        new_content = contents[:start] + \
            pretty_imports_block + \
            contents[end:]

        with open(agda_file, 'w') as file:
            file.write(new_content)

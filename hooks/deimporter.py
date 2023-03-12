from fix_imports import *
import os
import pathlib
import subprocess
import utils


if __name__ == "__main__":
    # Import remover

    # Checks every file, import statement by import statement, if they still typecheck if the statement is removed. If so, removes that statemet.

    # CAUTION! If the script is interrupted while running, you will likely end up with a missing import statement in the last inspected file.

    root = "src"
    status = 0
    agda_options = "--without-K --exact-split"

    agda_files = sorted(filter(lambda f: utils.isAgdaFile(pathlib.Path(
        f)) and os.path.dirname(f) != root, utils.get_files_recursively(root)))

    for i, agda_file in enumerate(agda_files):
        # If file doesn't compile, skip
        print(
            f"{str(i+1).rjust(len(str(len(agda_files))))} of {len(agda_files)}: '{agda_file}'", end="")

        # Now we need to find all imports, and then test one by one if they are used
        with open(agda_file, 'r', encoding='UTF-8') as file:
            contents = file.read()
            block, start, end = get_imports_block(contents)
            public, nonpublic, open_statements = categorize_imports(block)

            if nonpublic is None:
                print(f" Warning! Could not find imports. Skipping.")
                continue
            elif (subprocess.call(f"agda {agda_options} {agda_file}", shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0):
                print(f" ERROR! did not compile. Skipping.")
                continue
            else:
                print(" typechecked.")

            newnonpublic = set(nonpublic)

            for statement in nonpublic:
                newnonpublic.discard(statement)
                pretty_imports_block = prettify_imports_to_block(
                    public, newnonpublic, open_statements)

                new_content = contents[:start] + \
                    pretty_imports_block + \
                    contents[end:]

                with open(agda_file, 'w') as file:
                    file.write(new_content)

                if (subprocess.call(f"agda {agda_options} {agda_file}", shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0):
                    newnonpublic.add(statement)
                else:
                    print(f"    '{statement}' was unused")

            # Write final version
            pretty_imports_block = prettify_imports_to_block(
                public, newnonpublic, open_statements)

            new_content = contents[:start] + \
                pretty_imports_block + \
                contents[end:]

            with open(agda_file, 'w') as file:
                file.write(new_content)

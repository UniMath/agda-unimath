from fix_imports import *
import itertools
import os
import subprocess


def get_files(path):
    return os.listdir(path)


if __name__ == "__main__":
    # foundation to foundation-core import demoter
    # Only demotes imports in foundation and foundation-core modules

    root = "src"
    status = 0

    core_filenames = sorted(filter(lambda f: f.endswith(
        ".lagda.md"), get_files("src/foundation-core")))
    foundation_filenames = sorted(
        filter(lambda f: f.endswith(".lagda.md"), get_files("src/foundation")))
    foundation_and_core_files = tuple(itertools.chain(map(lambda f: os.path.join(root, "foundation", f),
                                                          foundation_filenames), map(lambda f: os.path.join(root, "foundation-core", f), core_filenames)))

    core_submodules = set(map(lambda f: f[:-len(".lagda.md")], core_filenames))

    for i, agda_file in enumerate(foundation_and_core_files):
        print(
            f"{str(i+1).rjust(len(str(len(foundation_and_core_files))))} of {len(foundation_and_core_files)}: '{agda_file}'", end="")

        with open(agda_file, 'r', encoding='UTF-8') as file:
            contents = file.read()
            block, start, end = get_imports_block(contents)
            public, nonpublic, open_statements = categorize_imports(block)

            if nonpublic is None:
                print(f" Warning! Could not find imports. Skipping.")
                continue
            elif (subprocess.call("agda " + agda_file, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0):
                print(f" ERROR! did not compile. Skipping.")
                continue
            else:
                print(" typechecked.")

            newnonpublic = set(nonpublic)

            # Subdivide imports into namespaces
            namespaces = subdivide_namespaces_imports(nonpublic)

            if not "foundation" in namespaces.keys():
                print("  No foundation imports.")
                continue

            for statement in namespaces["foundation"]:
                if (statement[len("foundation."):]) not in core_submodules:
                    continue

                newnonpublic.discard("open import " + statement)
                newnonpublic.add(
                    "open import " + statement.replace("foundation.", "foundation-core."))
                pretty_imports_block = prettify_imports_to_block(
                    public, newnonpublic, open_statements)

                new_content = contents[:start] + \
                    pretty_imports_block + \
                    contents[end:]

                with open(agda_file, 'w') as file:
                    file.write(new_content)

                if (subprocess.call("agda " + agda_file, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) != 0):
                    newnonpublic.discard(
                        "open import " + statement.replace("foundation.", "foundation-core."))
                    newnonpublic.add("open import " + statement)
                else:
                    print(
                        f"  '{statement}' can be imported from core")

            # Write final version
            pretty_imports_block = prettify_imports_to_block(
                public, newnonpublic, open_statements)

            new_content = contents[:start] + \
                pretty_imports_block + \
                contents[end:]

            with open(agda_file, 'w') as file:
                file.write(new_content)

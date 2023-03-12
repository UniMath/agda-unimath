from fix_imports import *
import itertools
import os
import utils

if __name__ == "__main__":
    # foundation to foundation-core import demoter

    # Checks every foundation and foundation-core file, for every import statement from foundation, if that file still typechecks of the import statement is replaced by importing from core. If so, keeps the change.

    # Note: Only demotes imports in foundation and foundation-core modules

    # CAUTION! If the script is interrupted while running, you will likely end up with a missing import statement in the last inspected file.

    root = "src"
    status = 0
    agda_options = "--without-K --exact-split"

    core_filenames = sorted(filter(lambda f: f.endswith(
        ".lagda.md"), os.listdir("src/foundation-core")))
    foundation_filenames = sorted(
        filter(lambda f: f.endswith(".lagda.md"), os.listdir("src/foundation")))
    foundation_filepaths = map(lambda f: os.path.join(root, "foundation", f), foundation_filenames)
    core_filepaths = map(lambda f: os.path.join(root, "foundation-core", f), core_filenames)
    foundation_and_core_files = tuple(itertools.chain(foundation_filepaths, core_filepaths))

    core_submodules = set(map(lambda f: f[:f.rfind(".lagda.md")], core_filenames))

    foundation_files_without_definitions = filter(lambda f: utils.has_no_definitions(os.path.join(root, "foundation", f)) and f[:f.rfind(".lagda.md")] in core_submodules, foundation_filenames)
    foundation_modules_without_definitions = set(map(lambda f: "foundation." + f[:f.rfind(".lagda.md")], foundation_files_without_definitions))

    print("The following modules can be fast-tracked, as they do not have any definitions:")
    print(foundation_modules_without_definitions)
    print()

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

                        # Subdivide imports into namespaces
            namespaces = subdivide_namespaces_imports(nonpublic)

            if not "foundation" in namespaces.keys():
                print(" has no foundation imports. Skipping.")
                continue

            if (utils.call_agda(agda_options, agda_file) != 0):
                print(f" ERROR! did not typeckec. Skipping.")
                continue
            else:
                print(" typechecked.")

            new_nonpublic = set(nonpublic)

            # Fast-track foundation files without definitions
            fast_track_modules = set()
            for module in namespaces["foundation"]:
                if module in foundation_modules_without_definitions:
                    statement = "open import " + module
                    new_nonpublic.discard(statement)
                    new_nonpublic.add(statement.replace("foundation.", "foundation-core."))
                    pretty_imports_block = prettify_imports_to_block(
                        public, new_nonpublic, open_statements)
                    fast_track_modules.add(module)

            if len(fast_track_modules) > 0:
                print(f'    {fast_track_modules} can immediately be imported from core')
                namespaces["foundation"] = namespaces["foundation"].difference(
                    fast_track_modules)

            # Others
            for module in namespaces["foundation"]:
                if (module[len("foundation."):]) not in core_submodules:
                    continue

                statement = "open import " + module
                new_nonpublic.discard(statement)
                new_nonpublic.add(statement.replace("foundation.", "foundation-core."))

                pretty_imports_block = prettify_imports_to_block(
                    public, new_nonpublic, open_statements)

                new_content = contents[:start] + \
                    pretty_imports_block + \
                    contents[end:]

                with open(agda_file, 'w') as file:
                    file.write(new_content)

                if (utils.call_agda(agda_options, agda_file) != 0):
                  new_nonpublic.discard(statement.replace("foundation.", "foundation-core."))
                  new_nonpublic.add(statement)
                else:
                    print(f"    '{module}' can be imported from core")

            # Write final version
            pretty_imports_block = prettify_imports_to_block(
                public, new_nonpublic, open_statements)

            new_content = contents[:start] + \
                pretty_imports_block + \
                contents[end:]

            with open(agda_file, 'w') as file:
                file.write(new_content)

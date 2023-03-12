#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/generate_namespace_index_modules.py

import os
import sys
import pathlib
import utils

root = "src"


def generate_title(namespace):
    return "# " + namespace.capitalize().replace("-", " ") + "\n"


def generate_imports(namespace):
    namespace_path = os.path.join(root, namespace)
    namespace_files = filter(lambda f: utils.isAgdaFile(
        pathlib.Path(os.path.join(namespace_path, f))), os.listdir(namespace_path))

    return "\n".join(sorted("open import " + namespace + "." + module_file[:module_file.index(".lagda.md")] + " public" for module_file in namespace_files))


agda_block_template = \
    '''```agda
module {namespace} where

{imports}
```
'''


def generate_agda_block(namespace):
    return agda_block_template.format(namespace=namespace, imports=generate_imports(namespace))


if __name__ == "__main__":
    status = 0
    for namespace in utils.get_subdirectories(root):
        namespace_filename = os.path.join(root, namespace) + ".lagda.md"
        with open(namespace_filename, "a+") as namespace_file:
            pass
        with open(namespace_filename, "r+") as namespace_file:
            contents = namespace_file.read()

        oldcontents = contents

        title_index = contents.find("# ")
        if title_index > 0:
            print(
                f"Warning! Namespace file {namespace_filename} has title after first line.")
        elif title_index == -1:  # Missing title. Generate it
            contents = generate_title(namespace) + contents

        agda_block_start = contents.rfind("```agda\n")
        if agda_block_start == -1:
            # Must add agda block
            # Add at the end of the file
            contents += "\n" + generate_agda_block(namespace)
        else:
            agda_block_end = contents.find(
                "\n```\n", agda_block_start + len("```agda\n"))
            if agda_block_end == -1:
                # An agda block is opened but not closed.
                # This is an error, but we can fix it
                print(
                    f"Warning! agda-block was opened but not closed in {namespace_filename}.")
                contents = contents[:agda_block_start] + \
                    generate_agda_block(namespace)
            else:
                contents = contents[:agda_block_start] + generate_agda_block(
                    namespace) + contents[agda_block_end+len("\n```\n"):]

        if (oldcontents != contents):
            status |= 1
            with open(namespace_filename, "w") as f:
                f.write(contents)
    sys.exit(status)

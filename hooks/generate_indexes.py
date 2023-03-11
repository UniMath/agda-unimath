#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/generate_indexes.py fileName.lagda.md

import os
import pathlib
import utils

status = 0
root = "src"

def get_subdirectories(startpath):
    for root, dirs, files in os.walk(startpath):
        for d in dirs:
            yield d


def get_files(path):
    return os.listdir(path)


def generate_title(namespace):
    return "# " + namespace.capitalize().replace("-", " ") + "\n"


def generate_imports(namespace):
    namespace_path = os.path.join(root, namespace)
    namespace_files = filter(lambda f: utils.isAgdaFile(
        pathlib.Path(os.path.join(namespace_path, f))), get_files(namespace_path))

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
    namespaces = get_subdirectories(root)
    for namespace in namespaces:
        with open(os.path.join(root, namespace) + ".lagda.md", "r+") as namespace_file:

            contents = namespace_file.read()

            title_index = contents.find("#")
            if title_index > 0:
                print(
                    f"Warning! Namespace file {namespace_file} has title after first line.")
            elif title_index == -1:  # Missing title. Generate it
                contents = generate_title(namespace) + contents

            agda_block_start = contents.find("```agda")
            if agda_block_start == -1:
                # Must add agda block
                # Add at the end of the file
                contents = contents + "\n" + generate_agda_block(namespace)
            else:
                agda_block_end = contents.find(
                    "```\n", agda_block_start + len("```agda"))
                if agda_block_end == -1:
                    # An agda block is opened but not closed.
                    # This is an error, but we can fix it
                    print(f"Warning! agda-block was opened but not closed in {namespace_file}.")
                    contents = contents[:agda_block_start] + \
                        generate_agda_block(namespace)
                else:
                    contents = contents[:agda_block_start] + generate_agda_block(
                        namespace) + contents[agda_block_end+len("```\n"):]
                    
            with open(os.path.join(root, namespace) + ".lagda.md", "w") as f:
              f.write(contents)

#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/generate_main_index.py

import os
import pathlib
import utils


def get_subdirectories(startpath):
    for root, dirs, files in os.walk(startpath):
        for d in dirs:
            yield d


def get_title(path):
    with open(path, "r") as file:
        contents = file.read()
        title_index = contents.find("# ")
        if title_index == -1:
            return None
        if title_index > 0:
            return None
        return contents[title_index + len("# "):contents.find("\n", len("# "))]


def get_files(path):
    return os.listdir(path)


entry_template = '- [{title}]({mdfile})'

def generate_namespace_entry_list(namespace):
    modules = sorted(get_files(os.path.join(root, namespace)))
    module_titles = map(lambda m: get_title(
        os.path.join(root, namespace, m)), modules)
    module_md = map(lambda m: (namespace + "." +
                       m.replace(".lagda.md", ".md")), modules)
    
    entry_list = ('  ' + entry_template.format(title = t, mdfile = md) for t, md in zip(module_titles, module_md))
    return entry_template.format(title = get_title(os.path.join(root, namespace) + ".lagda.md"), mdfile = namespace + ".md") + "\n" + "\n".join(entry_list)



def generate_index(root):
    return "# Formalization in Agda\n\n" + "\n\n".join(generate_namespace_entry_list(namespace) for namespace in sorted(get_subdirectories(root))) + "\n"


if __name__ == "__main__":
    
    root = "src"
    index_path = "INDEX.md"
    index_content = generate_index(root)

    with open(index_path, "w") as index_file:
        index_file.write(index_content)

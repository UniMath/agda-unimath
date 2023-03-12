#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/generate_main_index_file.py

import os
import sys

STATUS_FLAG_NO_TITLE = 1
STATUS_FLAG_DUPLICATE_TITLE = 2


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


def equivalence_classes(rel, it):
    partitions = []  # Found partitions
    for e in it:  # Loop over each element
        found = False  # Note it is not yet part of a know partition
        for p in partitions:
            if rel(e, p[0]):  # Found a partition for it!
                p.append(e)
                found = True
                break
        if not found:  # Make a new partition for it.
            partitions.append([e])
    return partitions


entry_template = '- [{title}]({mdfile})'


def generate_namespace_entry_list(namespace):
    status = 0
    modules = sorted(get_files(os.path.join(root, namespace)))
    module_titles = tuple(map(lambda m: get_title(
        os.path.join(root, namespace, m)), modules))
    module_mdfiles = tuple(map(lambda m: (namespace + "." +
                               m.replace(".lagda.md", ".md")), modules))

    # Check for missing titles
    for title, module in zip(module_titles, modules):
        if title is None:
            status |= STATUS_FLAG_NO_TITLE
            print(f"WARNING! {namespace}.{module} no title was found")

    # Check duplicate titles
    equal_titles = equivalence_classes(
        lambda tf1, tf2: tf1[0] == tf2[0], zip(module_titles, modules))
    equal_titles = tuple(filter(lambda ec: len(
        ec) > 1 and ec[0][0] is not None, equal_titles))

    if (len(equal_titles) > 0):
        status |= STATUS_FLAG_DUPLICATE_TITLE
        print(f"WARNING! Duplicate titles in {namespace}:")
        for ec in equal_titles:
            print(
                f"  Title '{ec[0][0]}': {', '.join(m[1][:-len('.lagda.md')] for m in ec)}")

    entry_list = ('  ' + entry_template.format(title=t, mdfile=md)
                  for t, md in sorted(zip(module_titles, module_mdfiles)))

    return entry_template.format(title=get_title(os.path.join(root, namespace) + ".lagda.md"), mdfile=namespace + ".md") + "\n" + "\n".join(entry_list), status


def generate_index(root):
    status = 0
    entry_lists = []
    for namespace in sorted(get_subdirectories(root)):
        entry_list, s = generate_namespace_entry_list(namespace)
        entry_lists.append(entry_list)
        status |= s

    return "# Formalisation in Agda\n\n" + "\n\n".join(entry_lists) + "\n", status


if __name__ == "__main__":

    status = 0
    root = "src"
    index_path = "INDEX.md"
    index_content, status = generate_index(root)

    with open(index_path, "w") as index_file:
        index_file.write(index_content)

    sys.exit(status)

#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/generate_main_index_file.py

import os
import sys
import utils

STATUS_FLAG_NO_TITLE = 1
STATUS_FLAG_DUPLICATE_TITLE = 2

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
    modules = sorted(os.listdir(os.path.join(root, namespace)))
    module_titles = tuple(map(lambda m: utils.get_lagda_file_title(
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

    return entry_template.format(title=utils.get_lagda_file_title(os.path.join(root, namespace) + ".lagda.md"), mdfile=namespace + ".md") + "\n" + "\n".join(entry_list), status

def generate_index(root, header):
    status = 0
    entry_lists = []
    for namespace in sorted(utils.get_subdirectories_recursive(root)):
        entry_list, s = generate_namespace_entry_list(namespace)
        entry_lists.append(entry_list)
        status |= s

    return f"{header}\n\n" + "\n\n".join(entry_lists) + "\n", status

if __name__ == "__main__":

    status = 0
    root = "src"

    index_path = "INDEX.md"
    index_header = "# Formalisation in Agda"

    index_content, status = generate_index(root, index_header)

    with open(index_path, "w") as index_file:
        index_file.write(index_content)

    sys.exit(status)

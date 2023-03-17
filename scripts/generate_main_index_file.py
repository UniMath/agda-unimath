#!/usr/bin/env python3
# Run this script:
# $ python3 scripts/generate_main_index_file.py

import os
import sys
import utils

STATUS_FLAG_NO_TITLE = 1
STATUS_FLAG_DUPLICATE_TITLE = 2

entry_template = '- [{title}]({mdfile})'


def generate_namespace_entry_list(namespace):
    status = 0
    modules = sorted(os.listdir(os.path.join(root, namespace)))
    module_titles = tuple(map(lambda m: utils.get_lagda_file_title(
        os.path.join(root, namespace, m)), modules))
    module_mdfiles = tuple(
        map(lambda m: utils.get_module_mdfile(namespace, m), modules))

    # Check for missing titles
    for title, module in zip(module_titles, modules):
        if title is None:
            status |= STATUS_FLAG_NO_TITLE
            print(f"WARNING! {namespace}.{module} no title was found")

    # Check duplicate titles
    equal_titles = utils.get_equivalence_classes(
        lambda tf1, tf2: tf1[0] == tf2[0], zip(module_titles, modules))
    equal_titles = tuple(filter(lambda ec: len(
        ec) > 1 and ec[0][0] is not None, equal_titles))

    if (len(equal_titles) > 0):
        status |= STATUS_FLAG_DUPLICATE_TITLE
        print(f"WARNING! Duplicate titles in {namespace}:")
        for ec in equal_titles:
            print(
                f"  Title '{ec[0][0]}': {', '.join(m[1][:m.rfind('.lagda.md')] for m in ec)}")

    module_titles_and_mdfiles = sorted(
        zip(module_titles, module_mdfiles), key=lambda tm: (tm[0].casefold(), tm[1]))

    entry_list = ('  ' + entry_template.format(title=t, mdfile=md)
                  for t, md in module_titles_and_mdfiles)

    namespace_title = utils.get_lagda_file_title(
        os.path.join(root, namespace) + ".lagda.md")
    namespace_entry = entry_template.format(
        title=namespace_title, mdfile=namespace + ".md")

    namespace_entry_list = namespace_entry + "\n" + "\n".join(entry_list)
    return namespace_entry_list, status


def generate_index(root, header):
    status = 0
    entry_lists = []
    for namespace in sorted(utils.get_subdirectories_recursive(root)):
        entry_list, s = generate_namespace_entry_list(namespace)
        entry_lists.append(entry_list)
        status |= s

    index = f"{header}\n\n" + "\n\n".join(entry_lists) + "\n"
    return index, status


summary_template = """
# SUMMARY

# Project

- [Agda-UniMath](HOME.md)
  - [Home](HOME.md)
  - [Community](CONTRIBUTORS.md)
    - [Maintainers](MAINTAINERS.md)
    - [Contributors](CONTRIBUTORS.md)
    - [Statement of inclusivity](STATEMENT-OF-INCLUSION.md)
    - [Projects using Agda-Unimath](USERS.md)
  - [How-to](HOWTO-INSTALL.md)
    - [Install](HOWTO-INSTALL.md)
    - [Cite the library](CITATION.cff)
  - [Guidelines](CODINGSTYLE.md)
    - [Structure your file](CONVENTIONS.md)
    - [Library coding style](CODINGSTYLE.md)
    - [Design principles](DESIGN-PRINCIPLES.md)
  - [Everything](everything.md)

{module_index}
"""

if __name__ == "__main__":

    root = "src"

    summary_path = "SUMMARY.md"
    index_header = "# Formalisation in Agda"

    index_content, status = generate_index(root, index_header)
    if status == 0:
        summary_contents = summary_template.format(module_index=index_content)
        with open(summary_path, "w") as summary_file:
            summary_file.write(summary_contents)
    sys.exit(status)

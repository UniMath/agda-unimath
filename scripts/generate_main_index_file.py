#!/usr/bin/env python3
# Run this script:
# $ ./scripts/generate_main_index_file.py

import os
import sys
import utils
import pathlib

STATUS_FLAG_NO_TITLE = 1
STATUS_FLAG_DUPLICATE_TITLE = 2

entry_template = '- [{title}]({mdfile})'


def generate_namespace_entry_list(namespace):
    status = 0

    file_names = sorted(os.listdir(os.path.join(root, namespace)))
    file_paths = map(lambda m: pathlib.Path(
        os.path.join(root, namespace, m)), file_names)
    lagda_file_paths = tuple(filter(utils.is_agda_file, file_paths))
    modules = tuple(map(lambda p: p.name, lagda_file_paths))
    module_titles = tuple(map(utils.get_lagda_md_file_title, lagda_file_paths))

    module_mdfiles = tuple(
        map(lambda m: utils.get_module_mdfile(namespace, m), modules))

    # Check for missing titles
    for title, module in zip(module_titles, modules):
        if title is None:
            status |= STATUS_FLAG_NO_TITLE
            print(
                f'WARNING! {namespace}.{module} no title was found', file=sys.stderr)

    # Check duplicate titles
    equal_titles = utils.get_equivalence_classes(
        lambda tf1, tf2: tf1[0] == tf2[0], zip(module_titles, modules))
    equal_titles = tuple(filter(lambda ec: len(
        ec) > 1 and ec[0][0] is not None, equal_titles))

    if (len(equal_titles) > 0):
        status |= STATUS_FLAG_DUPLICATE_TITLE
        print(f'WARNING! Duplicate titles in {namespace}:', file=sys.stderr)
        for ec in equal_titles:
            print(
                f"  Title '{ec[0][0]}': {', '.join(m[1][:m[1].rfind('.lagda.md')] for m in ec)}", file=sys.stderr)

    module_titles_and_mdfiles = sorted(
        zip(module_titles, module_mdfiles), key=lambda tm: (tm[1].split('.')))

    entry_list = ('  ' + entry_template.format(title=t, mdfile=md)
                  for t, md in module_titles_and_mdfiles)

    namespace_title = utils.get_lagda_md_file_title(
        os.path.join(root, namespace) + '.lagda.md')
    namespace_entry = entry_template.format(
        title=namespace_title, mdfile=namespace + '.md')

    namespace_entry_list = namespace_entry + '\n' + '\n'.join(entry_list)
    return namespace_entry_list, status


def generate_index(root, header):
    status = 0
    entry_lists = []
    namespaces = sorted(set(utils.get_subdirectories_recursive(root)))

    for namespace in namespaces:
        if namespace == 'temp':
            continue
        entry_list, s = generate_namespace_entry_list(namespace)
        entry_lists.append(entry_list)
        status |= s

    index = f'{header}\n\n' + '\n\n'.join(entry_lists) + '\n'
    return index, status


summary_template = """
# SUMMARY

# Overview

- [Overview](HOME.md)
  - [Home](HOME.md)
  - [Community](CONTRIBUTORS.md)
    - [Maintainers](MAINTAINERS.md)
    - [Contributors](CONTRIBUTORS.md)
    - [Statement of inclusivity](STATEMENT-OF-INCLUSION.md)
    - [Projects using Agda-Unimath](USERS.md)
    - [Grant acknowledgements](GRANT-ACKNOWLEDGEMENTS.md)
  - [Guides](HOWTO-INSTALL.md)
    - [Installing the library](HOWTO-INSTALL.md)
    - [Design principles](DESIGN-PRINCIPLES.md)
    - [Contributing to the library](CONTRIBUTING.md)
    - [Structuring your file](FILE-CONVENTIONS.md)
        - [File template](TEMPLATE.lagda.md)
    - [The library coding style](CODINGSTYLE.md)
    - [Citing the library](CITE-THIS-LIBRARY.md)

{module_index}
"""

if __name__ == '__main__':

    root = 'src'

    summary_path = 'SUMMARY.md'
    index_header = '# The agda-unimath library'

    index_content, status = generate_index(root, index_header)
    if status == 0:
        summary_contents = summary_template.format(module_index=index_content)
        with open(summary_path, 'w') as summary_file:
            summary_file.write(summary_contents)
    sys.exit(status)

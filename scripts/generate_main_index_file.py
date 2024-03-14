#!/usr/bin/env python3
# Run this script:
# $ ./scripts/generate_main_index_file.py

import os
import sys
import utils
import pathlib
import subprocess

STATUS_FLAG_GIT_ERROR = 1
STATUS_FLAG_NO_TITLE = 2
STATUS_FLAG_DUPLICATE_TITLE = 4

entry_template = '- [{title}]({mdfile})'


def generate_namespace_entry_list(root_path, namespace):
    status = 0

    try:
        git_tracked_files = utils.get_git_tracked_files()
    except subprocess.CalledProcessError:
        utils.eprint('Failed to get Git-tracked files')
        sys.exit(STATUS_FLAG_GIT_ERROR)

    namespace_path = root_path.joinpath(namespace)

    # Filter out the relevant files in the given namespace
    relevant_files = tuple(
        f for f in git_tracked_files if namespace_path in f.parents)

    lagda_file_paths = tuple(f for f in relevant_files if utils.is_agda_file(f))
    modules = tuple(p.name for p in lagda_file_paths)
    module_titles = tuple(utils.get_lagda_md_file_title(f)
                     for f in lagda_file_paths)
    module_mdfiles = tuple(utils.get_module_mdfile(namespace, m) for m in modules)

    # Check for missing titles
    for title, module in zip(module_titles, modules):
        if title is None:
            status |= STATUS_FLAG_NO_TITLE
            utils.eprint(
                f'WARNING! {namespace}.{module} no title was found')

    # Check duplicate titles
    equal_titles = utils.get_equivalence_classes(
        lambda tf1, tf2: tf1[0] == tf2[0], zip(module_titles, modules))
    equal_titles = tuple(filter(lambda ec: len(
        ec) > 1 and ec[0][0] is not None, equal_titles))

    if (len(equal_titles) > 0):
        status |= STATUS_FLAG_DUPLICATE_TITLE
        utils.eprint(f'WARNING! Duplicate titles in {namespace}:')
        for ec in equal_titles:
            utils.eprint(
                f"  Title '{ec[0][0]}': {', '.join(m[1][:m[1].rfind('.lagda.md')] for m in ec)}")

    module_titles_and_mdfiles = sorted(
        zip(module_titles, module_mdfiles), key=lambda tm: (tm[1].split('.')))

    entry_list = ('  ' + entry_template.format(title=t, mdfile=md)
                  for t, md in module_titles_and_mdfiles)

    namespace_title = utils.get_lagda_md_file_title(str(namespace_path.with_suffix('.lagda.md')))
    namespace_entry = entry_template.format(
        title=namespace_title, mdfile=namespace + '.md')

    namespace_entry_list = namespace_entry + '\n' + '\n'.join(entry_list)
    return namespace_entry_list, status


def generate_index(root_path, header):
    status = 0
    entry_lists = []
    namespaces = sorted(set(utils.get_subdirectories_recursive(root_path)))

    for namespace in namespaces:
        entry_list, s = generate_namespace_entry_list(root_path, namespace)
        entry_lists.append(entry_list)
        status |= s

    index = f'{header}\n\n' + '\n\n'.join(entry_lists) + '\n'
    return index, status


summary_template = """
<!--
This file is automatically generated. To add or change entries,
you need to change the template in ./scripts/generate_main_index_file.py
-->
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
    - [Guidelines for mixfix operators](MIXFIX-OPERATORS.md)
    - [Citing sources](CITING-SOURCES.md)
    - [Citing the library](CITE-THIS-LIBRARY.md)
  - [Library contents](SUMMARY.md)
  - [Art](ART.md)

{module_index}
"""

if __name__ == '__main__':

    root = 'src'

    summary_path = 'SUMMARY.md'
    index_header = '# The agda-unimath library'

    root_path = pathlib.Path(root)

    index_content, status = generate_index(root_path, index_header)
    if status == 0:
        summary_contents = summary_template.format(module_index=index_content)
        with open(summary_path, 'w') as summary_file:
            summary_file.write(summary_contents)
    sys.exit(status)

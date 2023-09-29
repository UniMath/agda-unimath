#!/usr/bin/env python3
# Run this script:
# $ ./scripts/fix_imports.py fileName.lagda.md

# * Remember to update the script's entry in `CONTRIBUTING.md` on changes

import collections
import sys
import utils


def get_imports_block(contents):
    start = contents.find('<details><summary>Imports</summary>')
    if start == -1:
        return None, start, -1
    end = contents.find('</details>', start)
    if end == -1:
        return None, start, end
    return contents[start:end], start, end


def categorize_imports(block):
    if block is None:
        return (None, None, None)
    # Strip all lines. There should not be any indentation in this block
    block = filter(lambda l: l != '', map(
        lambda l: l.strip(), block.split('\n')))
    # Don't want repeat import statements
    publicImports = set()
    nonPublicImports = set()
    openStatements = []

    for l in block:
        if len(l) == 0 or l.startswith('```') or '<details>' in l or '</details>' in l:
            continue
        if l.startswith('module') or l.startswith('{-# OPTIONS'):
            print(
                'Error: module declarations and pragmas cannot be in the details import block\n\
                Please put it in the first Agda block after the first header:\n\t' + str(fpath), file=sys.stderr)
            sys.exit(8)
        elif 'open import' in l:
            if l.endswith('public'):
                publicImports.add(l)
            else:
                nonPublicImports.add(l)
        elif 'open' in l:
            openStatements.append(l)
        else:
            raise ValueError('Unknown statement in details import block:\n\t' +
                             str(fpath))
    if len(openStatements) > 0:
        print(
            'Warning: Please review the imports block, it contains non-import statements:\n\t' + str(fpath), file=sys.stderr)

    return (publicImports, nonPublicImports, openStatements)


def subdivide_namespaces_imports(imports):
    # Subdivide imports into namespaces
    namespaces = collections.defaultdict(set)
    for statement in imports:
        namespace_start = statement.index(
            'open import') + len('open import') + 1
        module = statement[namespace_start:]
        try:
            namespace = module[:module.rindex('.')]
            namespaces[namespace].add(module)
        except ValueError:
            # Fall back when there is no `.`
            namespaces[module].add(module)

    # If the entire namespace is imported, no further imports from that namespace are needed
    for k in namespaces.keys():
        if k in namespaces[k]:
            namespaces[k] = {k}

    # If all of `foundation` is imported, no imports from `foundation-core` are needed
    if 'foundation' in namespaces['foundation']:
        namespaces.pop('foundation-core')

    # If a module is imported from `foundation` we don't need to import it from `foundation-core`
    if 'foundation' in namespaces.keys() and 'foundation-core' in namespaces.keys():
        for statement in namespaces['foundation']:
            submodule_start = statement.find('.')
            if submodule_start != -1:
                namespaces['foundation-core'].discard(
                    'foundation-core' + statement[submodule_start:])

    # Remove any namespaces without further imports
    return dict(filter(lambda kv: len(kv[1]) > 0, namespaces.items()))


def normalize_imports(imports):
    # Subdivide imports into namespaces
    namespaces = subdivide_namespaces_imports(imports)
    # Join together with the appropriate line separations
    blocks = ('\n'.join(map(lambda module: 'open import ' + module, sorted(namespace_imports)))
              for namespace, namespace_imports in sorted(namespaces.items()))

    return '\n\n'.join(blocks)


def get_imports(contents):
    block, start, end = get_imports_block(contents)
    return categorize_imports(block)


def prettify_imports(public, nonpublic, openstatements):
    return '\n\n'.join(filter(lambda ls: len(ls) > 0,
                              (normalize_imports(public), normalize_imports(nonpublic), '\n'.join(sorted(openstatements)))))


def prettify_imports_to_block(public, nonpublic, openstatements):
    pretty_imports = prettify_imports(public, nonpublic, openstatements)
    return '<details><summary>Imports</summary>\n' + \
        '\n```agda\n' + \
        pretty_imports + \
        '\n```\n\n'


def prettify_imports_block(block):
    public, nonpublic, openstatements = categorize_imports(block)
    return prettify_imports_to_block(public, nonpublic, openstatements)


if __name__ == '__main__':

    FLAG_NO_IMPORT_BLOCK = 1
    FLAG_IMPORT_BLOCK_HAS_PUBLIC = 2
    FLAG_IMPORT_MISSING_CLOSING_TAG = 4

    status = 0

    for fpath in utils.get_agda_files(sys.argv[1:]):

        with open(fpath, 'r', encoding='UTF-8') as file:
            contents = file.read()

        block, start, end = get_imports_block(contents)
        if block is None:
            if start != -1:
                print('Error: Agda import block is not closed with a `</details>` tag in:\n\t' +
                      str(fpath), file=sys.stderr)
                status |= FLAG_IMPORT_MISSING_CLOSING_TAG

            agdaBlockStart = utils.find_index(contents, '```agda')
            if len(agdaBlockStart) > 1:
                print('Warning: No Agda import block found inside <details> block in:\n\t' +
                      str(fpath), file=sys.stderr)
                status |= FLAG_NO_IMPORT_BLOCK
            continue

        public, nonpublic, openstatements = categorize_imports(block)
        pretty_imports_block = prettify_imports_to_block(
            public, nonpublic, openstatements)

        if public:
            print('Error: Import block contains public imports. These should be declared before the imports block:\n\t', str(
                fpath), file=sys.stderr)
            status |= FLAG_IMPORT_BLOCK_HAS_PUBLIC

        new_content = contents[:start] + \
            pretty_imports_block + \
            contents[end:]

        if contents != new_content:
            with open(fpath, 'w') as file:
                file.write(new_content)

    sys.exit(status)

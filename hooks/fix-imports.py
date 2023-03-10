#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/fix-imports.py fileName.lagda.md

from collections import defaultdict
import sys
import utils

status = 0

def normalize_imports(imports):
    # Subdivide imports into namespaces
    namespaces = defaultdict(set)
    for statement in imports:
        namespace_start = statement.index("open import") + len("open import") + 1
        module = statement[namespace_start:]
        try:
            namespace = module[:module.rindex(".")]
            namespaces[namespace].add(module)
        except ValueError:
            namespaces[module].add(module)

    # If the entire namespace is imported, no further imports from that namespace are needed
    for k in namespaces.keys():
        if k in namespaces[k]:
            namespaces[k] = {k}

    for statement in namespaces["foundation"]:
        submodule_start = statement.index(".")
        namespaces["foundation-core"].discard("foundation-core" + statement[submodule_start:])

    # Remove any namespaces that ended up being empty
    namespaces = dict(filter(lambda kv: len(kv[1]) > 0, namespaces.items()))

    # Join together with the appropriate line separations
    blocks = ("\n".join(map(lambda module: "open import " + module, sorted(namespace_imports))) for namespace, namespace_imports in sorted(namespaces.items()))

    return "\n\n".join(blocks)

for fpath in utils.agdaFiles(sys.argv[1:]):
    with open(fpath, 'r', encoding='UTF-8') as file:
        contents = file.read()
        start = contents.find('<details>')
        end = contents.find('</details>')
        if start != -1 and end != -1:
            block = contents[start:end]
            # Strip all lines. There should not be any indentation in this block
            newBlock = filter(lambda l: l != '', map(lambda l: l.strip(), block.split('\n')))

            # Don't want repeat import statements
            publicImports = set()
            nonPublicImports = set()
            openStatements = []

            for l in newBlock:
                if  len(l) == 0 or l.startswith('```') or '<details>' in l or '</details>' in l:
                    continue
                if l.startswith('module') or l.startswith('{-# OPTIONS'):
                    print(
                        'Error: module decl./pragmas can not be in the details import block\n\
                        Please put it in the first Agda block after the first header:\n\t' + str(fpath))
                    sys.exit(1)
                elif 'open import' in l:
                    if l.endswith('public'):
                        publicImports.add(l)
                    else:
                        nonPublicImports.add(l)
                elif 'open' in l:
                    openStatements.append(l)
                else:
                    print('Error: unknown statement in details import block:\n\t' + str(fpath))
            if len(openStatements) > 0:
                print(
                    'Warning: Please review the imports block, it contains non-import statements:\n\t' + str(fpath))
            imports = '\n\n'.join(
                filter(lambda ls: len(ls) > 0,
                    [normalize_imports(publicImports), normalize_imports(nonPublicImports), '\n'.join(sorted(openStatements))]))

            importBlock = '<details><summary>Imports</summary>\n' + \
                '\n```agda\n' +\
                imports + \
                '\n```\n\n'

            newContent = contents[:start] + \
                importBlock + \
                contents[end:]
            with open(fpath, 'w') as file:
                file.write(newContent)
        else:
            agdaBlockStart = utils.find_index(contents, '```agda')
            if len(agdaBlockStart) > 1:
                print(
                    'Warning: No Agda import block found inside <details> block in:\n\t' + str(fpath))
                status = 1
sys.exit(status)

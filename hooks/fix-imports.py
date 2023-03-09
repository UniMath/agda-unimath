#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/fix-imports.py fileName.lagda.md

from collections import defaultdict
import sys
import utils

status = 0

def sort_and_split_namespaces(imports):
    namespaces = defaultdict(set)
    for __import in imports:
        try:
            namespaces[__import[:__import.rindex(".")]].add(__import)
        except ValueError:
            namespaces[__import].add(__import)

    for k in namespaces.keys():
        if k in namespaces[k]: # The entire namespace is imported. Remove all other imports
            namespaces[k] = {k}

    for __import in namespaces["open import foundation"]:
        namespaces["open import foundation-core"].discard("open import foundation-core" + __import[__import.index("."):])

    namespaces = dict(filter(lambda kv: len(kv[1])>0, namespaces.items()))

    return "\n\n".join("\n".join(sorted(namespace_imports)) for k, namespace_imports in sorted(namespaces.items()))

for fpath in utils.agdaFiles(sys.argv[1:]):
    with open(fpath, 'r', encoding='UTF-8') as file:
        contents = file.read()
        start = contents.find('<details>')
        end = contents.find('</details>')
        if start != -1 and end != -1:
            block = contents[start:end]
            newBlock = filter(lambda l: l.strip() != '', block.split('\n'))
            publicImports = set()
            nonPublicImports = set()
            otherStuff = []

            for l in newBlock:
                if l.startswith('```') or len(l.strip()) == 0:
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
                    otherStuff.append(l)

            if len(otherStuff) > 0:

                print(
                    'Warning: Please review the imports block, it contains non-imports statements:\n\t' + str(fpath))
            imports = '\n\n'.join(
                filter(lambda ls: len(ls) > 0,
                    [sort_and_split_namespaces(publicImports), sort_and_split_namespaces(nonPublicImports), '\n'.join(sorted(otherStuff))]))

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

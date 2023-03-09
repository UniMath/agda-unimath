#!/usr/bin/env python3
# Run this script:
# $ python3 hooks/fix-imports.py fileName.lagda.md

import sys
import utils

status = 0

for fpath in utils.agdaFiles(sys.argv[1:]):
    with open(fpath, 'r', encoding='UTF-8') as file:
        contents = file.read()
        start = contents.find('<details>')
        end = contents.find('</details>')
        if start != -1 and end != -1:
            block = contents[start:end]
            newBlock = filter(lambda l: l.strip() != '', block.split('\n'))
            publicImports = []
            nonPublicImports = []
            otherStuff = []

            for l in newBlock:
                if l.startswith('```') or len(l.strip()) == 0:
                    continue
                if l.startswith('module') or l.startswith('{-# OPTIONS'):
                    print(
                        'Error: module decl./pragmas can not be in the details import block\n\
                        Please put it in the first Agda block after the first header:\n\t' + str(fpath) )
                    sys.exit(1)
                elif 'open import' in l:
                    if l.endswith('public'):
                        publicImports.append(l)
                    else:
                        nonPublicImports.append(l)
                elif 'open' in l:
                    otherStuff.append(l)

            if len(otherStuff) > 0:

                print(
                    'Warning: Please review the imports block, it contains non-imports statements:\n\t' + str(fpath) )
            imports = '\n'.join(
                map(lambda ls: '\n'.join(sorted(ls)),
                    filter(lambda ls: len(ls) > 0,
                           [
                        publicImports, nonPublicImports, otherStuff])))

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
            agdaBlockStart = utils.find_index(contents,'```agda')
            if len(agdaBlockStart) > 1:
                print('Warning: No Agda import block found inside <details> block in:\n\t' + str(fpath))
                status = 1
sys.exit(status)

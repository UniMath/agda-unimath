#!/usr/bin/env python3
# Run this script:
# $ ./scripts/spaces_convention.py fileName.lagda.md

# Hacky script to fix the spacing convention in the library

import sys
import utils
import re

if __name__ == '__main__':

    for fpath in utils.get_agda_files(sys.argv[1:]):

        with open(fpath, 'r') as f:
            contents = f.read()

        block_start = r'```agda\b'
        block_end = r'```\n'
        space_between = r'(\)|\}) *(\(|\{)'
        spaces_after = r'(\(|\{) *'
        spaces_before = r' *(\)|\})'
        # special cases
        dcurlyo = r'(\{{2,})'  # instances
        dcurlyc = r'(\}{2,})'
        opencd = r'\{-'
        closecd = r'-\}'
        holeo = r'\{!'
        holec = r'!\}'
        hole = r'\{!.*!\}'

        lines = contents.split('\n')
        for I, line in enumerate(lines):
            if re.match(block_start, line):
                current_block = []
                last_line = -1
                for J in range(I+1, len(lines)):
                    l = lines[J].rstrip()
                    if re.match(block_end, l):
                        last_line = J
                        break
                    else:
                        nspaces = len(l) - len(l.lstrip())
                        if nspaces & 1:
                            l = ' ' + l
                        current_block.append(l)

                block = '\n'.join(current_block)
                block = re.sub(opencd, r'@OPENSC@', block)
                block = re.sub(closecd, r'@CLOSESC@', block)
                block = re.sub(dcurlyo, r'@OPENDC@', block)
                block = re.sub(dcurlyc, r'@CLOSEDC@', block)
                block = re.sub(holeo, r'@OPENH@', block)
                block = re.sub(holec, r'@CLOSEH@', block)
                block = re.sub(spaces_after, r'\1 ', block)
                block = re.sub(spaces_before, r' \1', block)
                block = re.sub(space_between, r'\1 \2', block)
                block = re.sub(r'@OPENSC@', r'{-', block)
                block = re.sub(r'@CLOSESC@', r'-}', block)
                block = re.sub(r'@OPENDC@', r'{{', block)
                block = re.sub(r'@CLOSEDC@', r'}}', block)
                block = re.sub(r'@OPENH@', r'{!', block)
                block = re.sub(r'@CLOSEH@', r'!}', block)

                lines[I+1:last_line] = map(lambda x: x.rstrip(),
                                           block.split('\n'))
        new_contents = '\n'.join(lines)

        with open(fpath, 'w') as f:
            f.write(new_contents)

    sys.exit(0)

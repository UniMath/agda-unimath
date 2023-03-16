#!/usr/bin/env python3

import re
import utils
import sys

agda_block_pattern = r'```agda((.*)?\n)*```'

MSG = """{fpath}:{j}
Warning: Agda code block line exceeds 80 characters in width."""

if __name__ == "__main__":
    for fpath in utils.get_agda_files(sys.argv[1:]):
        with open(fpath, 'r') as f:
            contents = f.read()
        block_start = r'```agda\b'
        block_end = r'```'

        lines = contents.split('\n')
        for i, line in enumerate(lines):
            if re.match(block_start, line):
                code_lines = []
                for j in range(i + 1, len(lines)):
                    code_line = lines[j]
                    if len(code_line) > 80:
                        print(MSG.format(fpath=fpath, j=j))
                    if re.match(block_end, code_line):
                        break
                    else:
                        code_lines.append(code_line)
    sys.exit(0)

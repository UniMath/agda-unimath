#!/usr/bin/env python3
# Run this script:
# $ ./scripts/agda_conventions.py fileName.lagda.md

import sys
import utils
import re
import os
import collections

INDENT = '  '

unsolved_metas_pattern = re.compile(
    r'{-#\s*OPTIONS\s([^}]*\s)?--allow-unsolved-metas\s*#-}')
hole_pattern = re.compile(r'(^|[\s;{}()@".])\?($|[\s;{}()@".])|{!|!}')

if __name__ == '__main__':

    FLAG_LINE_COMMENT = 1
    FLAG_BLOCK_COMMENT = 2
    FLAG_ALLOW_UNSOLVED_METAS = 4
    FLAG_HOLE = 8

    status = 0
    offender_files = collections.Counter()

    for fpath in utils.get_agda_files(sys.argv[1:]):

        with open(fpath, 'r') as f:
            contents = f.read()
        lines = contents.split('\n')
        is_in_agda_block: bool = False
        block_comment_level: int = 0

        for i, line in enumerate(lines):
            is_tag, is_opening = utils.is_agda_opening_or_closing_tag(line)
            if is_tag:
                is_in_agda_block = is_opening
            elif is_in_agda_block:
                line, comment, block_comment_delta_pos, block_comment_delta_neg = utils.split_agda_line_comment_and_get_block_comment_delta(
                    line)

                block_comment_level += block_comment_delta_pos

                if comment:
                    status |= FLAG_LINE_COMMENT
                    offender_files[fpath] += 1
                    print(f"'{fpath}', line {i+1}: Line comments are disallowed.")

                if block_comment_delta_pos:
                    status |= FLAG_BLOCK_COMMENT
                    print(
                        f"'{fpath}', line {i+1}: Block comments are disallowed.")

                if block_comment_level == 0:

                    if unsolved_metas_pattern.search(line):
                        status |= FLAG_ALLOW_UNSOLVED_METAS
                        print(
                            f"'{fpath}', line {i+1}: The --allow-unsolved-metas flag is disallowed.")

                    if hole_pattern.search(line):
                        status |= FLAG_HOLE
                        print(
                            f"'{fpath}', line {i+1}: Agda holes are disallowed.")

                block_comment_level -= block_comment_delta_neg
                lines[i] = line + comment

    if status:

        print('\nTop offending files:')
        print(*map(lambda kv: f'  {kv[0]}: {kv[1]} violations',
                   sorted(offender_files.items(), key=lambda kv: kv[1])), sep='\n')

        print('\nTotal violations:', offender_files.total())

    sys.exit(status)

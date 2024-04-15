#!/usr/bin/env python3
# Run this script:
# $ ./scripts/even_indentation_conventions.py fileName.lagda.md

# Some simple to enforce space conventions
# * Remember to update the script's entry in `CONTRIBUTING.md` on changes

import sys
import utils
import re
import collections

AGDA_INDENT = '  '

even_indentation_pattern = re.compile(fr'^({AGDA_INDENT})*(\S|$)')


def is_even_indentation(line):
    return even_indentation_pattern.match(line)


if __name__ == '__main__':

    STATUS_UNEVEN_INDENTATION = 1

    status = 0

    offender_files: collections.Counter = collections.Counter()

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
                block_comment_delta_pos, block_comment_delta_neg = utils.get_block_comment_delta(
                    line)

                block_comment_level += block_comment_delta_pos

                if block_comment_level == 0:
                    # line = space_after_opening_parenthesis_on_new_line(line)

                    # Check even indentation
                    if not is_even_indentation(line):
                        if status == 0:
                            print('Error! Uneven indentation found')

                        print(f'{fpath}:line {i+1}')

                        offender_files[fpath] += 1
                        status |= STATUS_UNEVEN_INDENTATION

                block_comment_level -= block_comment_delta_neg

    if status & STATUS_UNEVEN_INDENTATION != 0:  # There were offending lines

        print('\nTop offending files:')
        print(*map(lambda kv: f'  {kv[0]}: {kv[1]} lines',
                   sorted(offender_files.items(), key=lambda kv: kv[1])), sep='\n')
        print(
            f'\nTotal number of lines in library unevenly indented: {sum(offender_files.values())}.\n\nUneven indentation means that there is code indented by a nonmultiple of the base indentation (2 spaces). If you haven\'t already, we suggest you set up your environment to more easily spot uneven indentation. For instance using VSCode\'s indent-rainbow extension.')

    sys.exit(status)

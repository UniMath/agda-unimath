#!/usr/bin/env python3
# Run this script:
# $ ./scripts/max_line_length_conventions.py fileName.md

# * Remember to update the script's entry in `CONTRIBUTING.md` on changes

import collections
import os
import re
import sys
import utils

named_module = r'^module\s\S+\swhere$'
open_import = r'^\s*open import '
# Forgives lines like this `( ( {{ my-very.long-token.that-is-too-long}})) =`
irreducible_line1 = r'^\s*([({⦃] ?)*[^\s;{}()@"]+[)}⦄]*( ?[^a-zA-Z\d\s"_({⦃][^\s"_.;(){}⦃@]?)?$'

forgive_patterns = (named_module, open_import, irreducible_line1)

forgive_regex = re.compile(
    '(' + ')|('.join(forgive_patterns) + ')')


def can_forgive_line(line):
    """
    Determines when a line can be forgiven for exceeding the character limit.
    """
    return bool(re.match(forgive_regex, line))


MSG = """  {fpath}:line {numline}"""


if __name__ == '__main__':

    MAX_LENGTH_EXCEEDED_FLAG: int = 1
    status: int = 0

    MAX_LINE_LENGTH: int = os.environ.get('MAX_LINE_LENGTH', 80)
    # CHECK_MAX_LENGTH: bool = os.environ.get('CHECK_MAX_LENGTH') == '1'

    # if CHECK_MAX_LENGTH:

    offender_files: collections.Counter = collections.Counter()

    for fpath in utils.get_agda_files(sys.argv[1:]):

        is_in_agda_block: bool = False
        block_comment_level: int = 0

        with open(fpath, 'r') as f:

            for numline, line in enumerate(f):
                line = line.rstrip()
                is_tag, is_opening = utils.is_agda_opening_or_closing_tag(line)
                if is_tag:
                    is_in_agda_block = is_opening
                elif is_in_agda_block:
                    # Consider the length of the line with the comment removed
                    line, comment, block_comment_delta_pos, block_comment_delta_neg = utils.split_agda_line_comment_and_get_block_comment_delta(
                        line)
                    line = line.rstrip()

                    # Ignore lines intersecting with block comments
                    block_comment_level += block_comment_delta_pos

                    if block_comment_level == 0 and len(line) > MAX_LINE_LENGTH and not can_forgive_line(line):
                        if status & MAX_LENGTH_EXCEEDED_FLAG == 0:
                            print(
                                f'The following lines exceed {MAX_LINE_LENGTH} characters in width:')
                        status |= MAX_LENGTH_EXCEEDED_FLAG
                        offender_files[fpath] += 1
                        print(MSG
                              .format(max=MAX_LINE_LENGTH,
                                      fpath=fpath,
                                      numline=numline + 1))

                    block_comment_level -= block_comment_delta_neg

    if status & MAX_LENGTH_EXCEEDED_FLAG != 0:  # There were offending lines

        print('\nTop offending files:')
        print(*map(lambda kv: f'  {kv[0]}: {kv[1]} lines',
                   sorted(offender_files.items(), key=lambda kv: kv[1])), sep='\n')
        print(
            f'\nTotal number of lines in library over character limit: {sum(offender_files.values())}.')
        print(
            f'Tip: if you haven\'t already, we recommend you enable a vertical ruler at the character limit ({MAX_LINE_LENGTH}) in your IDE.')
    sys.exit(status)

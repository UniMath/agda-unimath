#!/usr/bin/env python3

"""
To see the offending lines, run the following on your terminal:
    export CHECK_MAX_LENGTH=1
    make pre-commit
To deactivate the check, run:
    export CHECK_MAX_LENGTH=0
"""

import collections
import os
import re
import sys
import utils

named_module = re.compile(r'^module\s+\S+\s+where')
irreducible_line1 = re.compile(r'^\s*([({] )*[^\s.;{}()@"]+[)}]*$')
irreducible_line2 = re.compile(r'^\s*[^\s.;{}()@"]+ [:=]$')
comment_line = re.compile(r'^\s*--.*$')


def can_forgive_line(line):
    """
    Determines when a line of longer length than 80 characters can be forgiven.
    """

    return\
        line.startswith('open import ') or\
        named_module.match(line) or\
        irreducible_line1.match(line) or\
        irreducible_line2.match(line) or\
        comment_line.match(
            line)  # Comments should really not be there in the first place


MSG = """  {fpath}:line {numline}"""


if __name__ == '__main__':
    MAX_LENGTH_EXCEEDED_FLAG = 1
    status = 0

    CHECK_MAX_LENGTH: bool = os.environ.get('CHECK_MAX_LENGTH') == '1'
    MAX_LINE_LENGTH: int = os.environ.get('MAX_LINE_LENGTH', 80)

    if CHECK_MAX_LENGTH:

        is_in_agda_block: bool = False
        offender_files = collections.Counter()

        for fpath in utils.get_agda_files(sys.argv[1:]):
            with open(fpath, 'r') as f:
                contents = f.read()
            lines = contents.split('\n')
            for numline, line in enumerate(lines):
                if '```agda' in line:
                    is_in_agda_block = True
                elif '```' in line:
                    is_in_agda_block = False
                elif is_in_agda_block and\
                        len(line) > MAX_LINE_LENGTH and\
                        not can_forgive_line(line):

                    if status & MAX_LENGTH_EXCEEDED_FLAG == 0:
                        print(
                            f'The following lines exceed {MAX_LINE_LENGTH} characters in width:')
                    status |= MAX_LENGTH_EXCEEDED_FLAG
                    offender_files[fpath] += 1
                    print(MSG
                          .format(max=MAX_LINE_LENGTH,
                                  fpath=fpath,
                                  numline=numline + 1))
        print('\nTop offending files:')
        print(*map(lambda kv: f'  {kv[0]}: {kv[1]} lines',
              sorted(offender_files.items(), key=lambda kv: kv[1])), sep='\n')
        print(
            f'\nTotal number of lines in library over character limit: {sum(offender_files.values())}.')
    sys.exit(status)

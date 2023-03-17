#!/usr/bin/env python3

"""
To see the offending lines, run the following on your terminal:
    export CHECK_MAX_LENGTH=1
    make pre-commit
To deactivate the check, run:
    export CHECK_MAX_LENGTH=0
"""

import re
import utils
import sys
import os

CHECK_MAX_LENGTH: bool = os.environ.get('CHECK_MAX_LENGTH') == '1'
MAX_LINE_LENGTH_CHECK: int = os.environ.get('MAX_LINE_LENGTH_CHECK', 80)

MSG = """{fpath}:{numline}
Warning: Line exceeds {max}  characters in width."""


if __name__ == "__main__":
    if bool(CHECK_MAX_LENGTH):
        print("Checking for lines exceeding {max} characters in width.")
        for fpath in utils.get_agda_files(sys.argv[1:]):
            with open(fpath, 'r') as f:
                contents = f.read()
            lines = contents.split('\n')
            for numline, line in enumerate(lines):
                if len(line) > MAX_LINE_LENGTH_CHECK:
                    print(MSG
                          .format(max=MAX_LINE_LENGTH_CHECK,
                                  fpath=fpath,
                                  numline=numline + 1))
    sys.exit(0)

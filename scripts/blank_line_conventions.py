#!/usr/bin/env python3
# Run this script:
# $ python3 scripts/blank_line_conventions.py fileName.lagda.md

import sys
import utils
import re

open_tag_pattern = re.compile(r'^```\S+\n', flags=re.MULTILINE)
close_tag_pattern = re.compile(r'\n```$', flags=re.MULTILINE)


if __name__ == '__main__':

    status = 0

    for fpath in utils.get_agda_files(sys.argv[1:]):
        with open(fpath, 'r') as f:
            inputText = f.read()

        output = re.sub(r'[ \t]+$', '', inputText, flags=re.MULTILINE)
        output = re.sub(r'\n(\s*\n){2,}', '\n\n', output)

        # Remove blank lines after a code block starts, and blank lines before a code block ends
        # This only work properly in the absence of unspecified code blocks
        output = re.sub(
            r'\n{2,}```$', r'\n```', output, flags=re.MULTILINE)
        output = re.sub(
            r'^```(\S+)\n{2,}', r'```\1\n', output, flags=re.MULTILINE)

        # Empty blocks should have an empty line
        output = re.sub(r'^```(\S+)\n```$',
                        r'```\1\n\n```', output, flags=re.MULTILINE)

        if output != inputText:
            with open(fpath, 'w') as f:
                f.write(output)

    sys.exit(status)

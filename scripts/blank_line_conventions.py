#!/usr/bin/env python3
# Run this script:
# $ ./scripts/blank_line_conventions.py fileName.lagda.md

# * Remember to update the script's entry in `CONTRIBUTING.md` on changes

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

        # Remove blank lines before a `where`
        output = re.sub(r'\n(\s*\n)+(\s+)where(\s|$)',
                        r'\n\2where\3', output, flags=re.MULTILINE)

        # # Add blank line after `module ... where`
        # output = re.sub(r'(^([ \t]*)module[\s({][^\n]*\n(\2\s[^\n]*\n)*\2\s([^\n]*[\s)}])?where)\s*\n(?=\s*[^\n\s])', r'\1\n\n',
        #                 output, flags=re.MULTILINE)
        # # TODO: must match the first `where` after `module`

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

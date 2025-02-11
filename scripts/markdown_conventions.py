#!/usr/bin/env python3
# Run this script:
# $ ./scripts/markdown_conventions.py fileName.md

# * Remember to update the script's entry in `CONTRIBUTING.md` on changes

import sys
import utils
import re
import itertools


empty_block_pattern = re.compile(
    r'^```\S+.*\n(\s*\n)*\n```\s*$(?!\n(\s*\n)*</details>)', flags=re.MULTILINE)


def find_ill_formed_block(mdcode):
    """
    Checks if in a markdown file, every (specified) opening block tag is paired
    with a closing block tag before a new one is opened.

    Returns the line number of the first offending guard, as well as whether it is identified as a closing or opening guard.

    Note: This also disallows unspecified code blocks.
    """
    stack = []
    lines = mdcode.split('\n')

    for line_number, line in enumerate(lines, 1):
        line = line.strip()
        if line.startswith('```'):
            num_backticks = sum(
                1 for _ in itertools.takewhile(lambda x: x == '`', line))
            tag = line[num_backticks:]
            is_closing_guard = tag == ''
            if is_closing_guard:
                if stack and num_backticks == stack[-1]:
                    stack.pop()
                else:
                    return line_number, is_closing_guard
            elif not stack or num_backticks < stack[-1]:
                stack.append(num_backticks)
            else:
                return line_number, is_closing_guard
    return None, None


top_level_header_after_first_line = re.compile(r'\n#\s', flags=re.MULTILINE)

empty_section_nonincreasing_level = re.compile(
    r'^((#{2}\s([^\n]*)\n(\s*\n)*#{1,2})|(#{3}\s([^\n]*)\n(\s*\n)*#{1,3})|(#{4}\s([^\n]*)\n(\s*\n)*#{1,4})|(#{5}\s([^\n]*)\n(\s*\n)*#{1,5})|(#{6}\s([^\n]*)\n(\s*\n)*#{1,6})|(#{7}\s([^\n]*)\n(\s*\n)*#{1,7}))(?!#)', flags=re.MULTILINE)

empty_section_eof = re.compile(
    r'^(.*\n)*#+\s([^\n]*)\n(\s*\n)*$', flags=re.MULTILINE)

if __name__ == '__main__':

    STATUS_UNSPECIFIED_OR_ILL_FORMED_BLOCK = 1
    STATUS_TOP_LEVEL_HEADER_AFTER_FIRST_LINE = 2
    STATUS_EMPTY_SECTION = 4

    status = 0

    for fpath in utils.get_agda_files(sys.argv[1:]):
        with open(fpath, 'r') as f:
            inputText = f.read()

        output = inputText

        offender_line_number, offender_is_closing = find_ill_formed_block(
            output)

        if offender_line_number is not None:
            if offender_is_closing:
                print(
                    f"Error! File '{fpath}' line {offender_line_number} contains an untagged opening code guard, or a misplaced closing guard. Please note that untagged code blocks are disallowed.", file=sys.stderr)
            else:
                print(
                    f"Error! File '{fpath}' line {offender_line_number} contains an illegal opening code guard. This is likely because the previous code block should be closed when it is not. Otherwise, this code block needs to have a lower backtick level.", file=sys.stderr)

            status |= STATUS_UNSPECIFIED_OR_ILL_FORMED_BLOCK

        if top_level_header_after_first_line.search(output):
            print(
                f"Error! File '{fpath}' has a top level header after the first line. Please increase the header's level.")
            status |= STATUS_TOP_LEVEL_HEADER_AFTER_FIRST_LINE

        # Check for empty sections
        # TODO: print line numbers
        if empty_section_nonincreasing_level.search(output):
            print(
                f"Error! File '{fpath}' has an empty section. This may be caused by having a header with the wrong header level. If this was not by mistake, consider removing the section or including a sentence explaining why it is empty. For instance, depending on context, you may write 'This remains to be shown.'")

            status |= STATUS_EMPTY_SECTION

        if empty_section_eof.fullmatch(output):
            print(
                f"Error! File '{fpath}' has an empty section at the end of the file. Please consider removing the section or adding  a sentence explaining why it is empty. For instance, depending on context, you may write 'This remains to be shown.'")

            status |= STATUS_EMPTY_SECTION

        # Remove empty code blocks
        output = empty_block_pattern.sub('', output)

        # Remove punctuation in section headers
        output = re.sub(
            r'(^|\n)(#+\s.*)[\.,:;!?¡¿]\s*($|\n)', r'\1\2\3', output)

        # Replace strange whitespace with normal spaces
        output = re.sub(
            r'(?<!^)(?![ \t\r\n\f\v])\s', r' ', output)

        if output != inputText:
            with open(fpath, 'w') as f:
                f.write(output)

    sys.exit(status)

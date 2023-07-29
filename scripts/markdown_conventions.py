#!/usr/bin/env python3
# Run this script:
# $ ./scripts/markdown_conventions.py fileName.md

# * Remember to update the script's entry in `CONTRIBUTING.md` on changes

import sys
import utils
import re

open_tag_pattern = re.compile(r'^```\S+.*\n', flags=re.MULTILINE)
close_tag_pattern = re.compile(r'\n```$', flags=re.MULTILINE)

empty_block_pattern = re.compile(
    r'^```\S+.*\n(\s*\n)*\n```\s*$(?!\n(\s*\n)*</details>)', flags=re.MULTILINE)


def has_well_formed_blocks(mdcode, pos=0):
    """
    Checks if in a markdown file, every opening block tag is paired with a closing
    block tag before a new one is opened.

    Note: This also disallows unspecified code blocks.
    """

    if pos >= len(mdcode):
        return True

    open_match = open_tag_pattern.search(mdcode, pos)
    close_match = close_tag_pattern.search(mdcode, pos)

    if (open_match is None) != (close_match is None):
        # Open or closing tag but not both
        return False
    elif open_match is None:
        # No more blocks
        return True

    if close_match.start() < open_match.start():
        # A block is closed before it is opened
        return False

    # Check if multiple open tags
    second_open_match = open_tag_pattern.search(mdcode, open_match.end())
    if second_open_match is None:
        # Check for extra close tag
        return open_tag_pattern.search(mdcode, close_match.end()) is None
    elif second_open_match.start() < close_match.start():
        return False

    # Recurse
    return has_well_formed_blocks(mdcode, close_match.end())


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

        if not has_well_formed_blocks(output):
            print(
                f"Error! File '{fpath}' has an unspecified or ill-formed code block. Please note that unspecified code blocks are disallowed in this project. Otherwise, please check if there is an opening or closing code block tag (```) without a corresponding closing/opening tag.", file=sys.stderr)

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

        if output != inputText:
            with open(fpath, 'w') as f:
                f.write(output)

    sys.exit(status)

#!/usr/bin/env python3
# Run this script:
# $ python3 scripts/remove_extra_blank_lines.py fileName.lagda.md

import sys
import utils
import re


def recursive_sub(pattern, repl, string, flags=0):
    while re.search(pattern, string, flags=flags):
        string = re.sub(pattern, repl, string, flags=flags)
    return string


open_tag_pattern = re.compile(r"\n```(\S+)\n")
close_tag_pattern = re.compile(r"\n```\n")


def has_well_formed_blocks(mdcode, pos=0):
    """
    Checks if in a .md-file, every opening block tag is paired with a closing
    block tag before a new one is opened.
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

    return has_well_formed_blocks(mdcode, close_match.end())


if __name__ == "__main__":

    STATUS_FILES_WITH_UNEVEN_BLOCKS = 1

    status = 0

    for fpath in utils.get_agda_files(sys.argv[1:]):
        with open(fpath, "r") as f:
            inputText = f.read()
        output = recursive_sub(r"[ \t]+$", "", inputText, flags=re.MULTILINE)
        output = recursive_sub(r"\n\s*\n\s*\n", "\n\n", output)

        # Remove blank lines after a code block starts, and blank lines before a code block ends
        if not has_well_formed_blocks(output):
            print(
                f"Error! File '{fpath}' has ill-formed code blocks. Please check if there is an opening or closing code block tag (```) without a corresponding closing/opening tag.")

            status |= STATUS_FILES_WITH_UNEVEN_BLOCKS
        else:

            output = recursive_sub(r"\n\n```\n", "\n```\n", output)
            output = recursive_sub(r"\n```(\S+)\n\n", r"\n```\1\n", output)
            # Empty blocks should have an empty line
            output = recursive_sub(r"\n```(\S+)\n```\n",
                                   r"\n```\1\n\n```\n", output)

        with open(fpath, "w") as f:
            f.write(output)

    sys.exit(status)

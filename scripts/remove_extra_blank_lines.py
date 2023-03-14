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


def recursive_replace(string, old, new):
    while old in string:
        string = string.replace(old, new)
    return string


def len_iter(it):
    i = -1
    for i, el in enumerate(it):
        pass
    return i + 1


if __name__ == "__main__":

    STATUS_FILES_WITH_UNEVEN_BLOCKS = 1

    files_with_uneven_blocks = []
    status = 0

    for fpath in utils.get_agda_files(sys.argv[1:]):
        with open(fpath, "r") as f:
            inputText = f.read()
        output = recursive_sub(r"[ \t]+$", "", inputText, flags=re.MULTILINE)
        output = recursive_sub(r"\n\s*\n\s*\n", "\n\n", output)

        # Remove blank lines after a code block starts, and blank lines before a code block ends

        # Check if file starts/ends more blocks than it ends/starts
        block_starts = len_iter(re.finditer(r"\n```\S+\n", output))
        block_ends = len_iter(re.finditer(r"\n```\n", output))

        if block_starts != block_ends:
            if block_starts > block_ends:
                print(
                    f"Error! File '{fpath}' opens {block_starts} blocks but ends only {block_ends}.")
            else:
                print(
                    f"Error! File '{fpath}' opens only {block_starts} blocks but ends {block_ends}.")

            files_with_uneven_blocks.append(fpath)
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

#!/usr/bin/env python3
# Run this script:
# $ ./scripts/spaces_conventions_simple.py fileName.lagda.md

# Some simple to enforce space conventions
# * Remember to update the script's entry in `CONTRIBUTING.md` on expansion

import sys
import utils
import re


def no_repeat_whitespace_inside_line(line):
    return re.sub(r'(?<=\S)(?<!{!)\s{2,}(?=\S)(?!!})', ' ', line)


def space_after_special_symbols(line):
    return re.sub(r'([;)}])(?![@"\')}])(\S)', r'\1 \2', line)


def space_before_special_symbols(line):
    return re.sub(r'(?![.@"\'{(])(\S)([;{(])', r'\1 \2', line)


def no_whitespace_before_closing_parenthesis(line):
    return re.sub(r'(?<=\S)\s+\)', ')', line)


def no_whitespace_before_closing_curly_brace(line):
    return re.sub(r'(?![-!}])(\S)\s+\}', r'\1}', line)


def no_whitespace_after_opening_brace_inside_line(line):
    # TODO: this is very slow currently
    return utils.recursive_sub(r'^(\s*.*(?!--)[^\s({]{2,}.*[({])\s+', r'\1', line)


if __name__ == '__main__':

    status = 0

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
                line, comment, block_comment_delta_pos, block_comment_delta_neg = utils.split_agda_line_comment_and_get_block_comment_delta(
                    line)

                block_comment_level += block_comment_delta_pos

                if block_comment_level == 0:
                    line = no_repeat_whitespace_inside_line(
                        line)
                    line = space_after_special_symbols(line)
                    line = space_before_special_symbols(line)
                    line = no_whitespace_before_closing_parenthesis(line)
                    line = no_whitespace_before_closing_curly_brace(line)
                    # line = no_whitespace_after_opening_brace_inside_line(
                    #     line)
                    # line = space_after_opening_parenthesis_on_new_line(line)

                block_comment_level -= block_comment_delta_neg

                lines[i] = line + comment

        new_contents = '\n'.join(lines)
        if new_contents != contents:
            with open(fpath, 'w') as f:
                f.write(new_contents)

    sys.exit(status)

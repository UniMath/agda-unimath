#!/usr/bin/env python3
# Run this script:
# python3 scripts/spaces_convention_simple.py fileName.lagda.md
# Some simply enforcable space conventions

import sys
import utils
import re


def no_repeat_whitespace_inside_line(line):
    return re.sub(r'(\S)\s{2,}', r'\1 ', line)


def space_before_semicolon(line):
    return utils.recursive_sub(r'(?<=\S);', ' ;', line)


def space_after_semicolon(line):
    return utils.recursive_sub(r';(?=\S)', '; ', line)


def no_whitespace_before_closing_parenthesis(line):
    return utils.recursive_sub(r'(\S)\s+\)', r'\1)', line)


def no_whitespace_before_closing_curly_brace(line):
    return utils.recursive_sub(r'(?![-!}])(\S)\s+\}', r'\1}', line)


if __name__ == '__main__':

    agda_block_start = re.compile(r'^```agda\b')
    agda_block_end = re.compile(r'^```$')
    block_comment_start = re.compile(r'\{-(?!#)')
    block_comment_end = re.compile(r'(?<!#)-\}')

    for fpath in utils.get_agda_files(sys.argv[1:]):

        with open(fpath, 'r') as f:
            contents = f.read()

        is_in_agda_block = False
        block_comment_level = 0

        lines = contents.split('\n')
        for i, line in enumerate(lines):
            if agda_block_start.match(line):
                is_in_agda_block = True
            elif agda_block_end.match(line):
                is_in_agda_block = False
            elif is_in_agda_block:

                line, comment = utils.split_agda_line_comment(line)

                block_comment_level += len(
                    block_comment_start.findall(line))

                if block_comment_level == 0:
                    line = no_repeat_whitespace_inside_line(
                        line)
                    line = space_before_semicolon(line)
                    line = space_after_semicolon(line)
                    line = no_whitespace_before_closing_parenthesis(line)
                    line = no_whitespace_before_closing_curly_brace(line)
                    # line = space_after_opening_parenthesis_on_new_line(line)

                block_comment_level -= len(
                    block_comment_end.findall(line))
                line += comment
            lines[i] = line

        new_contents = '\n'.join(lines)

        if new_contents != contents:
            with open(fpath, 'w') as f:
                f.write(new_contents)

    sys.exit(0)

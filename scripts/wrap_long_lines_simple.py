#!/usr/bin/env python3
# Run this script:
# $ ./scripts/wrap_long_lines_simple.py fileName.lagda.md

# Wrap some easy to fix long lines
# * Remember to update the script's entry in `CONTRIBUTING.md` on changes

import sys
import utils
import re
import os
import max_line_length_conventions

INDENT = '  '


def check_wrap_line_type_signature(line):
    """
    Check if line is of the form
    ```agda
    my-very-long-verbose-term : Type-Stuff
    ```
    and if so add a line wrap after the colon.
    """
    m = re.fullmatch(r'((\s*)[^\s.;{}()@"]+\s+:)\s(.*)', line)
    if m:
        # Check that the next line is not indented more than this one
        # if i+1 >= len(lines) or not re.match(rf'^{m.group(2)}\s', lines[i+1]):
        line = f'{m.group(1)}\n{m.group(2)}{INDENT}{m.group(3)}'
    return line


def get_top_level_equality(line, open_delimiters='({', close_delimiters=')}'):
    stack = []
    mapping = dict(zip(close_delimiters, open_delimiters))

    for i, char in enumerate(line):
        if char in open_delimiters:
            stack.append(char)
        elif char in close_delimiters:
            if not stack or stack.pop() != mapping[char]:
                return None
        elif char == '=' and not stack and\
                (i == 0 or line[i-1] in ' })') and\
                (i+1 >= len(line) or line[i+1] in ' {('):
            return i


def check_wrap_line_definition(line):
    """
    Check if line is of the form
    ```agda
    pr1 (my-term-definition {A = A} x y z) a b = some-more-stuff
    ```
    and if so add a line wrap after the equals sign.
    """
    tle = get_top_level_equality(line)
    if tle and tle < len(line) - 1:
        m = re.fullmatch(r'((\s*)\S.*)', line[:tle+1])
        if m:
            # # Check that the next line is not indented more than this one
            # if i+1 >= len(lines) or not re.match(rf'^{m.group(2)}\s', lines[i+1]):
            line = f'{m.group(1)}\n{m.group(2)}{INDENT}{line[tle+1:].lstrip()}'
    return line


def check_wrap_line_definition_parameters(line):
    """
    Check if line is of the form
    ```agda
    my-term-definition {A = A} x y z =
    ```
    and if so add a line wrap after the first token.
    """
    tle = get_top_level_equality(line)
    if tle and tle == len(line) - 1:
        m = re.fullmatch(r'((\s*)[^\s.;{}()@"]+)\s+([^.;()@"]+\s+=)', line)
        if m:
            line = f'{m.group(1)}\n{m.group(2)}{INDENT}{m.group(3)}'
    return line


if __name__ == '__main__':

    MAX_LINE_LENGTH: int = os.environ.get('MAX_LINE_LENGTH', 80)

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

                if block_comment_level == 0 and \
                        len(line) > MAX_LINE_LENGTH and\
                        not max_line_length_conventions.can_forgive_line(line):

                    line = check_wrap_line_type_signature(line)
                    line = check_wrap_line_definition(line)
                    line = check_wrap_line_definition_parameters(line)

                block_comment_level -= block_comment_delta_neg
                lines[i] = line + comment

        new_contents = '\n'.join(lines)
        if new_contents != contents:
            with open(fpath, 'w') as f:
                f.write(new_contents)

    sys.exit(0)

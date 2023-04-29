#!/usr/bin/env python3
# Run this script:
# python3 scripts/easily_fixable_long_lines.py fileName.lagda.md
# Fix some easily fixable long lines

import sys
import utils
import re
import os
import max_line_length


def check_wrap_line_type_signature(line, i, lines):
    m = re.match(r'^((\s*)[^\s.;{}()@"]+\s+:)\s(.*)$', line)
    if m:
        # Check that the next line is not indented more than this one, just to be sure
        if i+1 >= len(lines) or not re.match(rf'^{m.group(2)}\s', lines[i+1]):
            line = f'{m.group(1)}\n{m.group(2)}  {m.group(3)}'
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
        elif char == '=' and not stack and i > 0 and i+1 < len(line) and line[i-1] in ' })' and line[i+1] in ' {(':
            return i


def check_wrap_line_definition(line, i, lines):
    tle = get_top_level_equality(line)
    if tle:
        m = re.match(r'^((\s*)\S.*)$', line[:tle+1])
        if m:
            # # Check that the next line is not indented more than this one, just to be sure
            # if i+1 >= len(lines) or not re.match(rf'^{m.group(2)}\s', lines[i+1]):
            line = f'{m.group(1)}\n{m.group(2)}  {line[tle+1:].lstrip()}'
    return line


def check_wrap_line_definition_parameters(line):
    m = re.match(r'^((\s*)[^\s.;{}()@"]+)\s+([^.;{}()@"]+\s+=)$', line)
    if m:
        line = f'{m.group(1)}\n{m.group(2)}  {m.group(3)}'
    return line


if __name__ == '__main__':

    agda_block_start = re.compile(r'^```agda\b')
    agda_block_end = re.compile(r'^```$')

    MAX_LINE_LENGTH: int = os.environ.get('MAX_LINE_LENGTH', 80)

    for fpath in utils.get_agda_files(sys.argv[1:]):

        with open(fpath, 'r') as f:
            contents = f.read()

        is_in_agda_block = False

        lines = contents.split('\n')
        for i, line in enumerate(lines):
            if agda_block_start.match(line):
                is_in_agda_block = True
            elif agda_block_end.match(line):
                is_in_agda_block = False
            elif is_in_agda_block:
                if len(line) > MAX_LINE_LENGTH and\
                        not max_line_length.can_forgive_line(line):
                    line = check_wrap_line_type_signature(line, i, lines)
                    line = check_wrap_line_definition(line, i, lines)
                    line = check_wrap_line_definition_parameters(line)
            lines[i] = line

        new_contents = '\n'.join(lines)

        if new_contents != contents:
            with open(fpath, 'w') as f:
                f.write(new_contents)

    sys.exit(0)

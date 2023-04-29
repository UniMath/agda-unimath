import re
import pathlib
import os
import subprocess


def get_files_recursive(startpath):
    """
    Recursively list all files in a directory and its subdirectories
    """
    for root, dirs, files in os.walk(startpath):
        # Yield the fully qualified path of each file
        yield from map(lambda f: os.path.join(root, f), files)


def get_subdirectories_recursive(startpath):
    for root, dirs, files in os.walk(startpath):
        yield from dirs


def find_index(s: str, t: str) -> list[int]:
    return [p for p, c in enumerate(s) if c == t]


def is_agda_file(f: pathlib.Path) -> bool:
    return (f.match('*.lagda.md') and
            f.exists() and
            f.is_file())


def get_agda_files(files: list[str]) -> list[pathlib.Path]:
    return list(filter(is_agda_file,
                       map(pathlib.Path, files)))


def extract_agda_code(lagda_filepath):
    """
    Extracts just the agda code from a literate agda markdown file.
    """
    contents = None
    with open(lagda_filepath, 'r') as lagda_file:
        contents = lagda_file.read()

    def find_blocks(loc=0):
        loc = contents.find('```agda\n', loc)
        if loc == -1:
            return
        block_start = loc + len('```agda\n')

        loc = contents.find('\n```', block_start)
        if loc == -1:
            yield contents[block_start:]
            return

        block_end = loc
        yield contents[block_start:block_end]

        yield from find_blocks(block_end + 1)

    return '\n\n'.join(find_blocks())


def has_no_definitions(lagda_filepath):
    """
    Determines if a literate agda markdown file doesn't have any definitions.
    This is done by checking if the agda code contains an equals sign '=' or a colon ':'.
    """
    agda_code = extract_agda_code(lagda_filepath)
    return '=' not in agda_code and ':' not in agda_code


def call_agda(options, filepath):
    return subprocess.call(f'agda {options} {filepath}', shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def get_lagda_md_file_title(lagda_filepath):
    with open(lagda_filepath, 'r') as file:
        contents = file.read()
        title_index = contents.find('# ')
        if title_index != 0:
            return None

        title_start = title_index + len('# ')
        title_end = contents.find('\n', len('# '))
        return contents[title_start:title_end]


def get_import_statement(namespace, module_file, public=False):
    return f"open import {namespace}.{module_file[:module_file.rfind('.lagda.md')]}{' public' * public}"


def get_module_mdfile(namespace, module_file):
    return namespace + '.' + module_file.replace('.lagda.md', '.md')


def get_agda_module_name(agda_file_path, root='src'):
    return agda_file_path[bool(root) * (len(root) + 1):agda_file_path.rfind('.lagda.md')].replace('/', '.').replace('\\', '.')


def get_equivalence_classes(equivalence_relation, iterable):
    partitions = []  # Found partitions
    for e in iterable:  # Loop over each element
        for p in partitions:
            if equivalence_relation(e, p[0]):  # Found a partition for it!
                p.append(e)
                break
        else:  # Make a new partition for it.
            partitions.append([e])
    return partitions


def recursive_sub(pattern, repl, string, flags=0):
    while re.search(pattern, string, flags=flags):
        string = re.sub(pattern, repl, string, flags=flags)
    return string


def split_agda_line_comment(line):
    in_pragma = 0
    in_block_comment = 0

    for match in re.finditer(r'(--)|(\{-#)|(#-\})|(\{-(?<!#))|((?!#)-\})', line):
        # Double dash
        if not in_pragma and not in_block_comment and match.group(1):
            comment_start = match.start()
            return line[:comment_start], line[comment_start:]
        elif match.group(2):  # Pragma start
            in_pragma += 1
        elif match.group(3):  # Pragma end
            in_pragma -= 1
        elif match.group(4):  # Block comment start
            in_block_comment += 1
        elif match.group(5):  # Block comment end
            in_block_comment -= 1

    return line, ''

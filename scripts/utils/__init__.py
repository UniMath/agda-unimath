import re
import pathlib
import os
import subprocess
import sys
from typing import List, Set

GITHUB_ROOT = 'https://github.com/'
GITHUB_REPO = 'UniMath/agda-unimath'


def github_page_for_commit(commit):
    return f'{GITHUB_ROOT}{GITHUB_REPO}/commit/{commit}'


def github_page_for_contributor(contributor):
    github_username = contributor.get('github')
    return github_username and f'{GITHUB_ROOT}{github_username}'


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def get_files_recursive(startpath):
    """
    Recursively list all files in a directory and its subdirectories
    """
    for root, dirs, files in os.walk(startpath):
        # Yield the fully qualified path of each file
        yield from map(lambda f: os.path.join(root, f), files)


def get_subdirectories_recursive(startpath):
    # Get list of Git-tracked files
    git_tracked_files = get_git_tracked_files()
    rootlen = len(str(startpath)) + 1
    # Filter out directories
    subdirectories = set()
    for path in git_tracked_files:
        if startpath in path.parents:
            relative_path = str(path.parent)[rootlen:]
            if relative_path:
                subdirectories.add(relative_path)

    return map(str, subdirectories)


def find_index(s: str, t: str) -> List[int]:
    return [p for p, c in enumerate(s) if c == t]


def is_agda_file(f: pathlib.Path) -> bool:
    return (f.match('*.lagda.md') and
            f.exists() and
            f.is_file())


def get_agda_files(files: List[str]) -> List[pathlib.Path]:
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
    This is done naively by checking if the agda code contains an equals sign '=' or a colon ':'.
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


agda_comment_regex = re.compile(
    r'(^--|(?<=[\s.;{}()@"])--)|(\{-#)|(#-\})|(\{-(?!#))|((?<!#)-\})')


def split_agda_line_comment_and_get_block_comment_delta(line):
    """
    Splits a line of agda code at a line comment, and also returns deltas on block comment level
    """
    in_pragma = 0
    block_comment_delta_pos = 0
    block_comment_delta_neg = 0

    for match in agda_comment_regex.finditer(line):
        # Double dash
        if not in_pragma and\
            not block_comment_delta_pos - block_comment_delta_neg\
                and match.group(1):
            comment_start = match.start()
            return line[:comment_start], line[comment_start:], block_comment_delta_pos, block_comment_delta_neg
        elif match.group(2):  # Pragma start
            in_pragma += 1
        elif match.group(3):  # Pragma end
            in_pragma -= 1
        elif match.group(4):  # Block comment start
            block_comment_delta_pos += 1
        elif match.group(5):  # Block comment end
            block_comment_delta_neg += 1

    return line, '', block_comment_delta_pos, block_comment_delta_neg


def get_block_comment_delta(line):
    """
    Returns deltas on block comment level
    """
    in_pragma = 0
    block_comment_delta_pos = 0
    block_comment_delta_neg = 0

    for match in agda_comment_regex.finditer(line):
        # Double dash
        if not in_pragma and\
            not block_comment_delta_pos - block_comment_delta_neg\
                and match.group(1):
            return block_comment_delta_pos, block_comment_delta_neg
        elif match.group(2):  # Pragma start
            in_pragma += 1
        elif match.group(3):  # Pragma end
            in_pragma -= 1
        elif match.group(4):  # Block comment start
            block_comment_delta_pos += 1
        elif match.group(5):  # Block comment end
            block_comment_delta_neg += 1

    return block_comment_delta_pos, block_comment_delta_neg


agda_block_tag_regex = re.compile(r'^```(agda)?((?=\s)|$)')


def is_agda_opening_or_closing_tag(line):
    """
    Returns two booleans.
    The first one signifies that the line is an opening or closing tag.
    The second boolean signifies whether it is an opening tag.
    """
    tag_match = agda_block_tag_regex.match(line)
    return bool(tag_match), tag_match and bool(tag_match.group(1))


def get_git_tracked_files():
    # Get list of Git-tracked files
    # Use the -z flag to prevent git from escaping non-ascii characters with
    # backslashes
    git_output = subprocess.check_output(['git', 'ls-files', '-z'], text=True)
    git_tracked_files = map(pathlib.Path, git_output.strip().split('\0')[:-1])
    return git_tracked_files

def get_git_last_modified(file_path):
    try:
        # Get the last commit date for the file
        output = subprocess.check_output(
            ['git', 'log', '-1', '--format=%at', file_path],
            stderr=subprocess.DEVNULL
        )
        output_str = output.strip()
        if output_str:
            return int(output_str)
        else:
            # Output is empty, file may be untracked
            return os.path.getmtime(file_path)
    except subprocess.CalledProcessError:
        # If the git command fails, fall back to filesystem modification time
        return os.path.getmtime(file_path)

def is_file_modified(file_path):
    try:
        subprocess.check_output(['git', 'diff', '--quiet', file_path], stderr=subprocess.DEVNULL)
        return False
    except subprocess.CalledProcessError:
        return True


def parse_agda_imports(agda_file: str) -> Set[str]:
    """Extract import statements from an Agda file."""
    imports = set()
    with open(agda_file, 'r', encoding='utf-8') as f:
        for line in f:
            match = re.match(r'^\s*open\s+import\s+([A-Za-z0-9\-.]+)', line)
            if match:
                imports.add(match.group(1))
    return imports

def count_lines_in_file(file_path: str) -> int:
    """Count lines of code in a file."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return sum(1 for _ in f)
    except Exception:
        return 0

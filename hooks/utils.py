import pathlib as path
import os
import subprocess

def find_index(s: str, t: str) -> list[int]:
    return [p for p, c in enumerate(s) if c == t]

def is_agda_file(f: path.Path) -> bool:
    return (f.match('*.lagda.md') and
            f.exists() and
            f.is_file())

def get_agda_files(files: list[str]) -> list[path.Path]:
    return list(filter(is_agda_file,
                       map(path.Path, files)))

def get_files_recursively(startpath):
    """
    Recursively list all files in a directory and its subdirectories
    """
    for root, dirs, files in os.walk(startpath):
        for file in files:
            # Yield the fully qualified path of each file
            yield os.path.join(root, file)

def extract_agda_code(lagda_filepath):
    """
    Extracts just the agda code from a literate agda markdown file.
    """
    contents = None
    with open(lagda_filepath, "r") as lagda_file:
        contents = lagda_file.read()

    def find_blocks(loc=0):
        loc = contents.find("```agda\n", loc)
        if loc == -1:
            return
        block_start = loc + len("```agda\n")

        loc = contents.find("\n```", block_start)
        if loc == -1:
            yield contents[block_start:]
            return

        block_end = loc
        yield contents[block_start:block_end]

        yield from find_blocks(block_end + 1)

    return "\n\n".join(find_blocks())

def has_no_definitions(lagda_filepath):
    """
    Determines if a literate agda markdown file doesn't have any definitions.
    This is done by checking if the agda code contains an equals sign '=' or a colon ':'.
    """
    agda_code = extract_agda_code(lagda_filepath)
    return '=' not in agda_code and ':' not in agda_code

def call_agda(options, filepath):
    return subprocess.call(f"agda {options} {filepath}", shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

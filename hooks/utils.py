import pathlib as path
import os

def find_index(s : str, t : str) -> list[int]:
    return [p for p, c in enumerate(s) if c == t]

def isAgdaFile(f: path.Path) -> bool:
    return (f.match('*.lagda.md') and
            f.exists() and
            f.is_file())

def agdaFiles(files: list[str]) -> list[path.Path]:
    return list(filter(isAgdaFile,
                       map(path.Path, files)))

def get_subdirectories_recursive(startpath):
    for root, dirs, files in os.walk(startpath):
        yield from dirs

def get_lagda_file_title(lagda_filepath):
    with open(lagda_filepath, "r") as file:
        contents = file.read()
        title_index = contents.find("# ")
        if title_index != 0:
            return None
        return contents[title_index + len("# "):contents.find("\n", len("# "))]

def get_import_statement(namespace, module_file, public=False):
    return f"open import {namespace}.{module_file[:module_file.find('.lagda.md')]}{' public' * public}"

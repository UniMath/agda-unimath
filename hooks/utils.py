import pathlib as path

def find_index(s : str, t : str) -> list[int]:
    return [p for p, c in  enumerate(s) if c == t]

def isAgdaFile(f: path.Path) -> bool:
    return (f.match('*.lagda.md') and
            f.exists() and
            f.is_file())

def agdaFiles(files: list[str]) -> list[path.Path]:
    return list(filter(isAgdaFile,
                       map(path.Path, files)))

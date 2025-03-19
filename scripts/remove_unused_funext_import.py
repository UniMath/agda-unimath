#!/usr/bin/env python3

import os
import re
import argparse
from pathlib import Path

# Import utils for Git-related functionality
import sys
import os.path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from scripts.utils import get_git_tracked_files

def find_agda_files(root_dir):
    """Find all Git-tracked Agda source files in the given directory tree."""
    # Get all Git-tracked files
    git_tracked_files = get_git_tracked_files()

    # Filter to keep only Agda files that are tracked by Git
    agda_files = []
    root_path = Path(root_dir).resolve()

    for file_path in git_tracked_files:
        full_path = Path(file_path)
        # Check if the file is in the specified root directory
        if root_path in full_path.resolve().parents or root_path == full_path.resolve().parent:
            if file_path.suffix == '.agda' or (file_path.suffix == '.md' and file_path.stem.endswith('.lagda')):
                agda_files.append(str(file_path))

    return agda_files

def process_file(file_path, dry_run=False):
    """
    Check if the file contains the import line but doesn't use function extensionality.
    Return True if the file was modified or would be modified.
    """
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Check if the file imports function-extensionality
    target_import = "open import foundation.function-extensionality\n"
    if target_import not in content:
        return False

    # Check if the file uses either 'eq-htpy' or 'funext'
    if 'eq-htpy' in content or 'funext' in content:
        return False

    # The file has the import but doesn't appear to use it
    if not dry_run:
        # Remove the import line and write the file back
        new_content = re.sub(f'^{re.escape(target_import)}', '', content, flags=re.MULTILINE)
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)

    return True

def main():
    parser = argparse.ArgumentParser(description='Remove unused function-extensionality imports')
    parser.add_argument('root_dir', help='Root directory of the Agda library')
    parser.add_argument('--dry-run', action='store_true',
                        help='Only report files that would be modified without changing them')
    args = parser.parse_args()

    print(f"Analyzing Git-tracked Agda files in {args.root_dir}...")
    agda_files = find_agda_files(args.root_dir)
    print(f"Found {len(agda_files)} tracked Agda files to check.")

    modified_files = []
    for file_path in agda_files:
        if process_file(file_path, args.dry_run):
            modified_files.append(file_path)

    if args.dry_run:
        print(f"\nDry run: {len(modified_files)} files would be modified to remove unused imports.")
    else:
        print(f"\nModified {len(modified_files)} files to remove unused function-extensionality imports.")

    if modified_files:
        print("\nModified files:")
        for file_path in modified_files:
            print(f"  - {file_path}")

if __name__ == "__main__":
    main()

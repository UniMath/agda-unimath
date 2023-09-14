#!/usr/bin/env python3

# This file is intended to be used as a mdbook preprocessor,
# and it adheres to the appropriate protocol; see
# https://rust-lang.github.io/mdBook/for_developers/preprocessors.html#hooking-into-mdbook

import json
import multiprocessing
import os
import subprocess
import sys

PROCESS_COUNT = 4
SOURCE_EXTS = ['.md', '.lagda.md']


def does_support(backend):
    return backend == 'html'


def module_source_path_from_md_name(roots, module_name):
    """
    Tries to find a source literate Agda or markdown file given
    a list of directories to seach, and a 'module name', which is an
    entry in the websites table of contents
    (usually of the form `agda-module.submodule.md`).

    Returns None if no such file is found.
    """
    base_name = module_name.replace('.', os.sep)[:-len('.md')]
    # Check agains "lagda", not ".lagda", since that period would
    # have been replaced by the previous line
    if base_name.endswith('lagda'):
        base_name = base_name[:-len('.lagda')]

    for root in roots:
        for ext in SOURCE_EXTS:
            full_path = f"{root}{bool(root) * '/'}{base_name}{ext}"
            if os.path.exists(full_path):
                return full_path
    return None


def get_author_element_for_file(filename):
    """
    Extracts git usernames of contributors to a particular file
    and formats it as an HTML element to be included on the page.
    """
    # Arguments mostly copied from the 1lab pipeline
    authors_git_output = subprocess.run([
        'git', 'shortlog',
        # Sort by number of commits and only print the contributor names
        '-ns',
        # Skip chore commits
        '--invert-grep', '--grep=^chore:',
        # Include authors and co-authors
        '--group=author', '--group=trailer:co-authored-by',
        # Limit to changes to the target file
        'HEAD', '--', filename
    ], capture_output=True, text=True, check=True).stdout
    author_names = [line[line.find('\t')+1:]
                    for line in authors_git_output.rstrip().split('\n')]
    if len(author_names) == 0:
        return ''
    return f'<p><i>Content created by {", ".join(author_names[:-1])}{(len(author_names) > 1) * " and "}{author_names[-1]}</i></p>'


def add_author_info_to_chapter_rec_mut(roots, chapter, visited):
    """
    Modifies chapter's content to reflect its git contributors,
    and recurses to subchapters to do the same.
    """
    # We still want to recurse to visited files, because
    # "source file" does not necessarily correspond to index tree entry
    # i.e. there can be two index tree entries pointing to the same file,
    # but they may have different subentries
    # (e.g. "CONTRIBUTORS.md" at the time of writing)
    source_path = chapter['source_path']
    add_author_info_to_sections_rec_mut(roots, chapter['sub_items'], visited)
    if source_path in visited:
        return

    visited.add(source_path)
    potential_source_file_name = module_source_path_from_md_name(
        roots, source_path)
    if potential_source_file_name is None:
        print('No source filename found, skipping',
              chapter['name'], source_path, file=sys.stderr)
        return

    source_file_name = potential_source_file_name

    author_element = get_author_element_for_file(source_file_name)
    chapter['content'] += '\n' + author_element


def add_author_info_to_sections_rec_mut(roots, sections, visited):
    """
    Recursively modifies a list of book sections to make all
    included chapters contain information on their contributors.
    """
    for section in sections:
        chapter = section.get('Chapter')
        if chapter is None:
            continue

        add_author_info_to_chapter_rec_mut(roots, chapter, visited)


def add_author_info_to_root_section(roots, section, visited):
    """
    Recursively modifies a section to make all included chapters
    contain information on their contributors, then returns the section.
    """
    chapter = section.get('Chapter')
    if chapter is not None:
        add_author_info_to_chapter_rec_mut(roots, chapter, visited)

    return section


if __name__ == '__main__':
    if len(sys.argv) > 1:
        arguments = sys.argv[1:]
        # Indicate with the exit code whether the preprocessor supports the
        # given backend or not
        if arguments[0] == 'supports':
            if not does_support(arguments[1]):
                sys.exit(1)
            else:
                sys.exit(0)

    # Load the book contents from standard input
    context, book = json.load(sys.stdin)

    # Split the work between PROCESS_COUNT processes
    with multiprocessing.Pool(PROCESS_COUNT) as p:
        book['sections'] = p.starmap(add_author_info_to_root_section, [
            (['src', ''], section, set())
            for section in book['sections']
        ])

    # Pass the book back to mdbook
    json.dump(book, sys.stdout)

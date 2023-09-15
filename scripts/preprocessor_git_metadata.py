#!/usr/bin/env python3

# This file is intended to be used as a mdbook preprocessor,
# and it adheres to the appropriate protocol; see
# https://rust-lang.github.io/mdBook/for_developers/preprocessors.html#hooking-into-mdbook

from collections import defaultdict
import json
from multiprocessing import Pool
import os
import subprocess
import sys
import tomli

PROCESS_COUNT = 4
SOURCE_EXTS = ['.md', '.lagda.md']
RECENT_CHANGES_COUNT = 5
CONTRIBUTORS_FILE = 'scripts/contributors_data.toml'

# Lazily initialized
contributors_data = None


def get_real_author(raw_username):
    return next((c for c in contributors_data if raw_username in c['usernames']), None)


def does_support(backend):
    return backend == 'html'


def print_skipping_contributor_warning(contributor):
    print('Warning: not attributing changes to', contributor,
          f'. If you want your work to be attributed to you, add yourself to {CONTRIBUTORS_FILE}',
          file=sys.stderr)


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

    # I wish there was a way to bulk these log commands into one,
    # but alas I haven't found anything to that effect

    # Arguments mostly copied from the 1lab pipeline
    raw_authors_git_output = subprocess.run([
        'git', 'shortlog',
        # Sort by number of commits and only print the contributor names
        '-ns',
        # Skip chore commits
        '--invert-grep', '--grep=^chore:',
        # Include authors and co-authors
        '--group=author', '--group=trailer:co-authored-by',
        # Limit to changes to the target file
        'HEAD', '--', filename
    ], capture_output=True, text=True, check=True).stdout.splitlines()

    # Collect authors and sort by number of commits
    author_commits = defaultdict(int)
    for raw_author_line in raw_authors_git_output:
        commit_count_str, raw_author = raw_author_line.split('\t')
        commit_count = int(commit_count_str.strip())
        author = get_real_author(raw_author)
        if author is None:
            print_skipping_contributor_warning(raw_author)
            continue
        author_commits[author['displayName']] += commit_count
    author_names = sorted(author_commits, key=author_commits.get, reverse=True)
    attribution_text = ', '.join(author_names[:-1]) + (len(author_names) > 1) * ' and ' + author_names[-1]

    file_log_output = subprocess.run([
        'git', 'log',
        # Only print the date
        '--format=%as',
        'HEAD', '--', filename
    ], capture_output=True, text=True, check=True).stdout.splitlines()
    created_date = file_log_output[-1]
    modified_date = file_log_output[0]

    recent_changes_output = subprocess.run([
        'git', 'log',
        # Show only last RECENT_CHANGES_COUNT commits
        '-n', str(RECENT_CHANGES_COUNT),
        # Get hash, author, date and message, separated by tabs
        '--format=%h%x09%an%x09%as%x09%s',
        'HEAD', '--', filename
    ], capture_output=True, text=True, check=True).stdout.splitlines()
    recent_changes = '## Recent changes\n'
    for recent_changes_line in recent_changes_output:
        [sha, raw_author, date, message] = recent_changes_line.split('\t')
        author = get_real_author(raw_author)
        if author is None:
            print_skipping_contributor_warning(raw_author)
            continue
        recent_changes += f'- <i>{sha}</i> ({author["displayName"]}) [{date}] - {message}\n'

    return (
        f'<p><i>Content created by {attribution_text}</i></p><p>Created: {created_date}; Last modified: {modified_date}</p>',
        recent_changes
    )


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
    was_visited = source_path in visited
    visited.add(source_path)
    add_author_info_to_sections_rec_mut(roots, chapter['sub_items'], visited)
    if was_visited:
        return

    potential_source_file_name = module_source_path_from_md_name(
        roots, source_path)
    if potential_source_file_name is None:
        print('No source filename found, skipping',
              chapter['name'], source_path, file=sys.stderr)
        return

    source_file_name = potential_source_file_name

    header_info_element, footer_info_element = get_author_element_for_file(
        source_file_name)
    # Assumption: The title is the first header in the file
    chapter_heading_start = chapter['content'].index('# ')
    chapter_heading_end = chapter['content'].index('\n', chapter_heading_start)
    # Insert the authors after the first heading
    chapter['content'] = chapter['content'][:chapter_heading_end] + '\n' + header_info_element + \
        chapter['content'][chapter_heading_end:] + '\n' + footer_info_element


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

    # Load the contributors data
    with open(CONTRIBUTORS_FILE, 'rb') as f:
        contributors_data = tomli.load(f)['contributors']

    # Load the book contents from standard input
    context, book = json.load(sys.stdin)

    # Split the work between PROCESS_COUNT processes
    with Pool(PROCESS_COUNT) as p:
        book['sections'] = p.starmap(add_author_info_to_root_section, [
            (['src', ''], section, set())
            for section in book['sections']
        ])

    # Pass the book back to mdbook
    json.dump(book, sys.stdout)

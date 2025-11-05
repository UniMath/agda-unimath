#!/usr/bin/env python3

# This file is intended to be used as a mdbook preprocessor,
# and it adheres to the appropriate protocol; see
# https://rust-lang.github.io/mdBook/for_developers/preprocessors.html#hooking-into-mdbook

import json
from multiprocessing import Pool
import os
import subprocess
import sys
from utils import github_page_for_commit, eprint
from utils.contributors import parse_contributors_file, format_multiple_authors_attribution, get_real_author_index, sorted_authors_from_raw_shortlog_lines, print_skipping_contributors_warning

PROCESS_COUNT = 4
SOURCE_EXTS = ['.md', '.lagda.md']
RECENT_CHANGES_COUNT = 5


def does_support(backend):
    return backend == 'html'


def module_source_path_from_md_name(roots, module_name):
    """
    Tries to find a source literate Agda or markdown file given
    a list of directories to search, and a 'module name', which is an
    entry in the websites table of contents
    (usually of the form `agda-module.submodule.md`).

    Returns None if no such file is found.
    """
    base_name = module_name.replace('.', os.sep)[:-len('.md')]
    # Check against "lagda", not ".lagda", since that period would
    # have been replaced by the previous line
    if base_name.endswith('lagda'):
        base_name = base_name[:-len('.lagda')]

    for root in roots:
        for ext in SOURCE_EXTS:
            full_path = f"{root}{bool(root) * '/'}{base_name}{ext}"
            if os.path.exists(full_path):
                return full_path
    return None


def cleanup_author_part(raw_author):
    stripped = raw_author.strip()
    # Assumption: The user doesn't have a name containing '<'
    email_start = raw_author.find('<')
    if email_start > 0:
        return stripped[:email_start - 1]
    return stripped


def nobreak_span(text):
    return f'<span class="prefer-nobreak">{text}</span>'


def get_recent_changes(contributors, *args):
    """
    Returns a markdown list of the most recent RECENT_CHANGES_COUNT commits.
    """
    recent_changes_output = subprocess.run([
        'git', 'log',
        # Show only last RECENT_CHANGES_COUNT commits
        '-n', str(RECENT_CHANGES_COUNT),
        # Get hash, date, message, author and coauthors, separated by tabs
        # NB When there are no trailers, the line ends with a tab
        # NB Coauthors usually have the format "name <email>" and there is
        #    no way to tell git to strip the email, so it needs to be done
        #    in post processing
        '--format=%H%x09%as%x09%s%x09%an%x09%(trailers:key=co-authored-by,valueonly=true,separator=%x09)',
        'HEAD',
        *args
    ], capture_output=True, text=True, check=True).stdout.splitlines()

    skipped_authors = set()
    recent_changes = '## Recent changes\n'

    for line in recent_changes_output:
        [sha, date, message, *raw_authors] = line.split('\t')
        author_indices = []
        for raw_author in map(cleanup_author_part, raw_authors):
            if raw_author == '':
                continue
            author_index = get_real_author_index(raw_author, contributors)
            if author_index is None:
                skipped_authors.add(raw_author)
                continue
            author_indices.append(author_index)

        if not author_indices:
            continue

        formatted_authors = format_multiple_authors_attribution([
            contributors[idx]['displayName'] for idx in author_indices
        ])
        recent_changes += f'- {date}. {formatted_authors}. <i><a target="_blank" href={github_page_for_commit(sha)}>{message}.</a></i>\n'

    return (recent_changes, skipped_authors)


def get_author_element_for_file(filename, include_contributors, contributors, contributors_file):
    """
    Extracts git usernames of contributors to a particular file
    and formats it as an HTML element to be included on the page.
    """

    # I wish there was a way to bulk these log commands into one,
    # but alas I haven't found anything to that effect

    attribution_text = ''
    skipped_authors = set()

    if include_contributors:
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

        # If all commits to a file are chore commits, then there are no authors
        if raw_authors_git_output:
            # Collect authors and sort by number of commits
            sorted_authors, __skipped_authors = sorted_authors_from_raw_shortlog_lines(
                raw_authors_git_output, contributors)
            skipped_authors.update(__skipped_authors)
            author_names = [
                author['displayName']
                for author in sorted_authors
            ]
            attribution_text = f'<p><i>Content created by {format_multiple_authors_attribution(author_names)}.</i></p>'

    file_log_output = subprocess.run([
        'git', 'log',
        # Only print the date
        '--format=%as',
        'HEAD', '--', filename
    ], capture_output=True, text=True, check=True).stdout.splitlines()
    created_date = file_log_output[-1]
    modified_date = file_log_output[0]

    recent_changes, skipped_authors = get_recent_changes(
        contributors, '--', filename)

    if skipped_authors:
        print_skipping_contributors_warning(skipped_authors, contributors_file)

    return (
        f'{attribution_text}<p><i>{nobreak_span("Created on " + created_date)}.</i><br><i>{nobreak_span("Last modified on " + modified_date)}.</i></p>',
        recent_changes
    )


def add_author_info_to_chapter_rec_mut(roots, chapter, contributors, config):
    """
    Modifies chapter's content to reflect its git contributors,
    and recurses to subchapters to do the same.
    """
    source_path = chapter['source_path']
    add_author_info_to_sections_rec_mut(
        roots, chapter['sub_items'], contributors, config)

    potential_source_file_name = module_source_path_from_md_name(
        roots, source_path)
    if potential_source_file_name is None:
        eprint('No source filename found, skipping',
               chapter['name'], source_path)
        return

    source_file_name = potential_source_file_name

    if source_file_name in config['suppress_processing']:
        # Suppress processing for this page
        return

    if source_file_name in config['sitewide_changes']:
        # Insert recent sitewide changes on page
        footer_recent_sitewide, skipped_authors = get_recent_changes(
            contributors, '--invert-grep', '--grep=^chore:')

        if skipped_authors:
            print_skipping_contributors_warning(
                skipped_authors, config['contributors_file'])

        # Append to end of file
        chapter['content'] += '\n' + footer_recent_sitewide
        return

    header_info_element, footer_info_element = get_author_element_for_file(
        source_file_name,
        any((source_file_name.endswith(ext)
            for ext in config['attribute_file_extensions'])),
        contributors,
        config['contributors_file'])

    # Assumption: The title is the first header in the file
    chapter_heading_start = chapter['content'].index('# ')
    chapter_heading_end = chapter['content'].index('\n', chapter_heading_start)
    # Insert the authors after the first heading
    chapter['content'] = chapter['content'][:chapter_heading_end] + '\n' + header_info_element + \
        chapter['content'][chapter_heading_end:] + '\n' + footer_info_element


def add_author_info_to_sections_rec_mut(roots, sections, contributors, config):
    """
    Recursively modifies a list of book sections to make all
    included chapters contain information on their contributors.
    """
    for section in sections:
        chapter = section.get('Chapter')
        if chapter is None:
            continue

        add_author_info_to_chapter_rec_mut(
            roots, chapter, contributors, config)


def add_author_info_to_root_section(roots, section, contributors, config):
    """
    Recursively modifies a section to make all included chapters
    contain information on their contributors, then returns the section.
    """
    chapter = section.get('Chapter')
    if chapter is not None:
        add_author_info_to_chapter_rec_mut(
            roots, chapter, contributors, config)

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
    metadata_config = context['config']['preprocessor']['git-metadata']
    metadata_config['attribute_file_extensions'] = metadata_config.get(
        'attribute_file_extensions', [])
    metadata_config['suppress_processing'] = metadata_config.get(
        'suppress_processing', [])
    metadata_config['sitewide_changes'] = metadata_config.get(
        'sitewide_changes', [])
    metadata_config['contributors_file'] = metadata_config.get(
        'contributors_file', 'CONTRIBUTORS.toml')

    # Load the contributors data
    contributors_data = parse_contributors_file(
        metadata_config['contributors_file'])

    if bool(metadata_config.get('enable')):
        # Split the work between PROCESS_COUNT processes
        with Pool(PROCESS_COUNT) as p:
            book['sections'] = p.starmap(add_author_info_to_root_section, [
                (['src', '',  'docs'], section, contributors_data, metadata_config)
                for section in book['sections']
            ])
    else:
        eprint('Skipping git metadata, enable option was set to',
               metadata_config.get('enable'))

    # Pass the book back to mdbook
    json.dump(book, sys.stdout)

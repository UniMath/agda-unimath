#!/usr/bin/env python3

# This file is intended to be used as a mdbook preprocessor,
# and it adheres to the appropriate protocol; see
# https://rust-lang.github.io/mdBook/for_developers/preprocessors.html#hooking-into-mdbook

import json
import re
import sys
import time
from utils import eprint

CONCEPT_REGEX = re.compile(
    r'\{\{#concept (?:WD=(\w+) )?"(.*?)"\}\}')

LINK_REGEX = re.compile(
    r'\[(.*?)\]\(.*\)')

def does_support(backend):
    return backend == 'html'

def sub_match_for_concept(m, mut_index, path):
    wikidata_id = m.group(1)
    text = m.group(2)
    plaintext = LINK_REGEX.sub(r'\1', text)
    index_entry = {
        'name': plaintext,
        'text': text
    }
    anchor = ''
    if wikidata_id is not None:
        index_entry['wikidata'] = wikidata_id
        index_entry['link'] = f'{path[:-2]}html#{wikidata_id}'
        anchor = f'<a id="{wikidata_id}" style="display:none;" class="wikidata">{plaintext}</a>'
    mut_index.append(index_entry)
    return f'{anchor}<b>{text}</b>'

def tag_concepts_chapter_rec_mut(chapter, config, mut_index):
    chapter['content'] = CONCEPT_REGEX.sub(
        lambda m: sub_match_for_concept(m, mut_index, chapter['path']),
        chapter['content'])
    tag_concepts_sections_rec_mut(chapter['sub_items'], config, mut_index)

def tag_concepts_sections_rec_mut(sections, config, mut_index):
    for section in sections:
        chapter = section.get('Chapter')
        if chapter is None:
            continue

        tag_concepts_chapter_rec_mut(chapter, config, mut_index)

def tag_concepts_root_section(section, config, mut_index):
    chapter = section.get('Chapter')
    if chapter is not None:
        tag_concepts_chapter_rec_mut(chapter, config, mut_index)

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
    concepts_config = context['config']['preprocessor']['concepts']

    # Thread the index through execution
    mut_index = []
    start = time.time()
    if bool(concepts_config.get('enable', True)) == True:
        book['sections'] = list(map(
            lambda s: tag_concepts_root_section(s, concepts_config, mut_index),
            book['sections']))
    else:
        eprint('Skipping concept tagging, enable option was',
               concepts_config.get('enable'))

    end = time.time()
    eprint(end - start)

    if mut_index != []:
        with open(concepts_config.get('output-file', 'concept_index.json'), 'w') as index_f:
            json.dump(mut_index, index_f)

    # Pass the book back to mdbook
    json.dump(book, sys.stdout)

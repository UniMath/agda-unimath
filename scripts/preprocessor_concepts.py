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
    r'\{\{#concept "([^=\n"]+)"(.*?)\}\}')

WIKIDATA_ID_REGEX = re.compile(
    r'WDID=(\S+)')

WIKIDATA_LABEL_REGEX = re.compile(
    r'WD="([^=\n"]+)"')

DISAMBIGUATION_REGEX = re.compile(
    r'Disambiguation="([^=\n"]+)"')

AGDA_REGEX = re.compile(
    r'Agda=(\S+)')

LINK_REGEX = re.compile(
    r'\[(.*?)\]\(.*\)')

EXTERNAL_LINKS_REGEX = re.compile(
    r'## External links\s+')

LEFTOVER_CONCEPT_REGEX = re.compile(r'\{\{#concept.*')

# Python's html.escape transforms a single quote into &#x27;, but Agda
# transforms it into &#39;, so we just rewrite the replacement ourselves.
#
# https://github.com/jaspervdj/blaze-markup/blob/master/src/Text/Blaze/Renderer/String.hs#L25
ESCAPE_TRANSLATION_TABLE = str.maketrans({
    '<': '&lt;',
    '>': '&gt;',
    '&': '&amp;',
    '"': '&quot;',
    "'": '&#39;'
})


def agda_escape_html(string):
    return string.translate(ESCAPE_TRANSLATION_TABLE)


def make_definition_regex(definition):
    return re.compile(
        r'<a id="(\d+)" href="[^"]+" class="[^"]+">' + re.escape(agda_escape_html(definition)) + r'</a>')


def make_loose_definition_regex(definition):
    escaped = re.escape(definition)
    return re.compile(
        escaped + r'\s+:(?=[\s({])|' +
        r'(?:data|record|infix[lr]?(?:\s+\d+)?)\s+' + escaped
    )


def does_support(backend):
    return backend == 'html' or backend == 'linkcheck'


def match_wikidata_id(meta_text):
    m = WIKIDATA_ID_REGEX.search(meta_text)
    if m is None:
        return None
    return m.group(1)


def match_wikidata_label(meta_text):
    m = WIKIDATA_LABEL_REGEX.search(meta_text)
    if m is None:
        return None
    return m.group(1)


def match_disambiguation(meta_text):
    m = DISAMBIGUATION_REGEX.search(meta_text)
    if m is None:
        return None
    return m.group(1)


def match_agda_name(meta_text):
    m = AGDA_REGEX.search(meta_text)
    if m is None:
        return None
    return m.group(1)


def get_definition_id(name, content):
    definition_regex = make_definition_regex(name)
    m = definition_regex.search(content)
    if m is None:
        return None
    return m.group(1)


def slugify_markdown(md):
    text = md.replace(' ', '-')
    for markup_char in ['*', '_', '~', '(', ')']:
        text = text.replace(markup_char, '')
    return text


def sup_link_reference(href, content, brackets=True, new_tab=False):
    # f-strings can't contain backslashes, so we can't escape the quotes
    link_target = new_tab * ' target="_blank"'
    return f'<sup>{brackets * "["}<a href="{href}"{link_target} class="concept">{content}</a>{brackets * "]"}</sup>'


def sub_match_for_concept(m, mut_index, mut_error_locations, config, path, initial_content):
    text = m.group(1)
    metadata = m.group(2)
    wikidata_id = match_wikidata_id(metadata)
    wikidata_label = match_wikidata_label(metadata)
    disambiguation = match_disambiguation(metadata)
    agda_name = match_agda_name(metadata)
    plaintext = LINK_REGEX.sub(r'\1', text)
    url_path = path[:-2] + 'html'
    entry_name = plaintext
    if disambiguation is not None:
        entry_name += ' (' + disambiguation + ')'
    index_entry = {
        'name': entry_name,
        'text': text
    }
    anchor = ''
    target = ''
    target_id = f'concept-{slugify_markdown(plaintext)}'
    references = []

    has_wikidata_id = wikidata_id is not None and wikidata_id != 'NA'
    has_wikidata_label = wikidata_label is not None

    if '$' in text:
        eprint('Warning: LaTeX fragments are not supported in concept tags:', text)
        mut_error_locations.add(path)

    if has_wikidata_id:
        index_entry['wikidata'] = wikidata_id
        target_id = wikidata_id

        if has_wikidata_label:
            index_entry['__wikidata_label'] = wikidata_label
        else:
            eprint('Warning: Wikidata identifier', wikidata_id,
                   'provided for "' + entry_name + '"',
                   'without a corresponding label in', path)
            mut_error_locations.add(path)
    else:
        if has_wikidata_label:
            eprint('Warning: Wikidata label', wikidata_label,
                   'provided for "' + entry_name + '"',
                   'without a corresponding identifier in', path)
            mut_error_locations.add(path)
    if agda_name is not None:
        found_def = False
        if config.get('skip-agda', False):
            # Agda is not preprocessed, look at the text for approximation
            loose_regex = make_loose_definition_regex(agda_name)
            m = loose_regex.search(initial_content)
            if m is not None:
                found_def = True
        else:
            target_id = f'concept-{agda_name}'
            agda_id = get_definition_id(agda_name, initial_content)
            if agda_id is not None:
                destination = f'{url_path}#{agda_id}'
                index_entry['definition'] = destination
                found_def = True
        if not found_def:
            eprint('Warning: Concept definition not found:',
                   plaintext, '; expected', agda_name, 'to exist in',
                   path)
            mut_error_locations.add(path)
    anchor += f'<a id="{target_id}" class="concept"></a>'
    index_entry['link'] = f'{url_path}#{target_id}'
    # For now the link is the best thing we have as an identifier
    # - it should be unique (for a given point in time), and
    #   with the way we generate `target_id` it should be as stable
    #   as we can get
    index_entry['id'] = index_entry['link']
    references.append(sup_link_reference(f'#{target_id}', '¶', False))
    mut_index.append(index_entry)
    return f'{anchor}<b>{text}</b>{"".join(reversed(references))}'


def tag_concepts_chapter_rec_mut(chapter, config, mut_index, mut_error_locations):
    mut_local_index = []
    chapter['content'] = CONCEPT_REGEX.sub(
        lambda m: sub_match_for_concept(
            m, mut_local_index, mut_error_locations, config, chapter['path'], chapter['content']),
        chapter['content'])
    leftover_concepts = LEFTOVER_CONCEPT_REGEX.findall(chapter['content'])
    if len(leftover_concepts) != 0:
        eprint(
            f'Warning: the following concept invocations were not recognized in {chapter["path"]}:')
        mut_error_locations.add(chapter['path'])
        for line in leftover_concepts:
            eprint('  ' + line)
    external_references = []
    for entry in mut_local_index:
        wikidata_label = entry.pop('__wikidata_label', None)
        wikidata_id = entry.get('wikidata', None)
        if wikidata_label is not None and wikidata_id is not None:
            wikidata_link = config.get(
                'wikidata-template').format(wikidata_id=wikidata_id)
            external_references.append(
                f'<a href="{wikidata_link}">{wikidata_label.capitalize()}</a> at Wikidata')
        mut_index.append(entry)
    if external_references != []:
        formatted_references = ''.join(
            map(lambda a: f'- {a}\n', external_references))
        external_links_location = EXTERNAL_LINKS_REGEX.search(
            chapter['content'])
        if external_links_location is not None:
            insert_at = external_links_location.end()
            chapter['content'] = chapter['content'][:insert_at] + \
                formatted_references + chapter['content'][insert_at:]
        else:
            chapter['content'] += f'\n## External links\n\n{formatted_references}'
    tag_concepts_sections_rec_mut(
        chapter['sub_items'], config, mut_index, mut_error_locations)


def tag_concepts_sections_rec_mut(sections, config, mut_index, mut_error_locations):
    for section in sections:
        chapter = section.get('Chapter')
        if chapter is None:
            continue

        tag_concepts_chapter_rec_mut(
            chapter, config, mut_index, mut_error_locations)


def tag_concepts_root_section(section, config, mut_index, mut_error_locations):
    chapter = section.get('Chapter')
    if chapter is not None:
        tag_concepts_chapter_rec_mut(
            chapter, config, mut_index, mut_error_locations)

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
    mut_error_locations = set()
    if bool(concepts_config.get('enable', True)) == True:
        book['sections'] = list(map(
            lambda s: tag_concepts_root_section(
                s, concepts_config, mut_index, mut_error_locations),
            book['sections']))
        if len(mut_error_locations) != 0:
            eprint('The following files contain errors:')
            for location in mut_error_locations:
                eprint('  ' + location)
            sys.exit(1)
    else:
        eprint('Skipping concept tagging, enable option was set to',
               concepts_config.get('enable'))

    if mut_index != []:
        with open(concepts_config.get('output-file', 'concept_index.json'), 'w') as index_f:
            json.dump(mut_index, index_f)

    # Pass the book back to mdbook
    json.dump(book, sys.stdout)

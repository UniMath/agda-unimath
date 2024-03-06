#!/usr/bin/env python3

# This file is intended to be used as a mdbook preprocessor,
# and it adheres to the appropriate protocol; see
# https://rust-lang.github.io/mdBook/for_developers/preprocessors.html#hooking-into-mdbook

import re
import pybtex
import pybtex.database
import pybtex.plugin
import pybtex.backends
import pybtex.style.formatting
import pybtex.style.formatting.alpha
import pybtex.style.labels.alpha
import sys
import io
from utils import eprint
import json


CITEAS_FIELD = 'citeas'

# Regex to match citation macros
CITE_REGEX = re.compile(r'\{\{#cite ([^\}\s]+)(?:\s(.*))?\}\}')
NO_REF_CITE_REGEX = re.compile(r'\bno-ref(erence)?\b')
REFERENCE_REGEX = re.compile(r'\{\{#reference ([^\}\s]+)(?:\s(.*?))?\}\}')


def render_references(bib_database : pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle , backend: pybtex.backends.BaseBackend, cited_keys):
    formatted_bibliography = style.format_bibliography(bib_database, sorted(cited_keys))
    output = io.StringIO()
    backend.write_to_stream(formatted_bibliography, output)
    html = output.getvalue()

    for cite_key in cited_keys:
        cite_entry = bib_database.entries[cite_key]
        label = style.label_style.format_label(cite_entry)
        formatted_label = format_label(bib_database.entries[cite_key], style)
        html = html.replace(f'<dt>{label}</dt>', f'<dt class="reference-entry"><b><a name="reference-{formatted_label}">[{formatted_label}]</a></b></dt>')

    return html

def format_label(entry : pybtex.database.Entry, style: pybtex.style.formatting.BaseStyle):
    if CITEAS_FIELD in entry.fields.keys():
        return entry.fields[CITEAS_FIELD]
    else:
        return style.label_style.format_label(entry)


def format_citation(bib_database : pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle , backend: pybtex.backends.BaseBackend, match, cited_keys):
    cite_key = match.group(1)
    if not match.group(2) or not NO_REF_CITE_REGEX.search(match.group(2)):
        cited_keys.add(cite_key)
    # Function to format the citation and collect cited keys
    if cite_key in bib_database.entries:
        cite_entry = bib_database.entries[cite_key]

        label = style.label_style.format_label(cite_entry)
        formatted_label = format_label(cite_entry, style)

        return f'<a  style="color: black; text-decoration: none;" class="citation-link" href="#reference-{label}">[{formatted_label}]</a>'
    else:
        eprint(f"Warning: Citation key '{cite_key}' not found in bibliography.")
        return None

def generate_bibliography(bib_database : pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle , backend: pybtex.backends.BaseBackend, cited_keys):
    eprint(cited_keys)
    # Function to generate the bibliography section
    if cited_keys:
        return render_references(bib_database, style, backend, cited_keys)
    else:
        return ""

def process_citations_chapter_rec_mut(chapter, bib_database : pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle , backend):
    cited_keys = set()  # Set to keep track of all cited keys
    content = chapter.get('content', '')
    new_content = CITE_REGEX.sub(lambda match: format_citation(bib_database, style, backend, match, cited_keys) or match.group(0), content)

    for match in REFERENCE_REGEX.finditer(content):
        cited_keys.add(match.group(1))
    new_content = REFERENCE_REGEX.sub('', new_content)


    if cited_keys:
        bibliography_section = generate_bibliography(bib_database, style, backend, cited_keys)
        eprint(bibliography_section)
        if bibliography_section:
            new_content = insert_bibliography_at_correct_location(new_content, bibliography_section)

    chapter['content'] = new_content

    process_citations_sections_rec_mut(chapter['sub_items'], bib_database, style, backend)

def insert_bibliography_at_correct_location(content, bibliography_section):
    references_heading = "## References"
    pattern = re.compile(r'^## .+$')
    start_index = content.find(references_heading)

    if start_index != -1:
        # Find end of the References section by locating the next heading
        end_index = pattern.search(content, start_index + len(references_heading))
        if end_index:
            insertion_point = end_index.start()
        else:
            insertion_point = len(content)
        new_content = content[:insertion_point] + "\n\n" + bibliography_section + "\n\n" + content[insertion_point:]
    else:
        # If there's no References section, append it at the end
        new_content = content + "\n\n" + references_heading + "\n\n" + bibliography_section

    return new_content

def process_citations_sections_rec_mut(sections, bib_database, style: pybtex.style.formatting.BaseStyle, backend: pybtex.backends.BaseBackend):
    for section in sections:
        chapter = section.get('Chapter')
        if chapter is None:
            continue

        process_citations_chapter_rec_mut(chapter, bib_database, style, backend)


def process_citations_root_section(section, bib_database : pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle, backend: pybtex.backends.BaseBackend):
    chapter = section.get('Chapter')
    if chapter is not None:
        process_citations_chapter_rec_mut(chapter, bib_database, style, backend)

    return section

def does_support_backend(backend):
    return backend == 'html'

if __name__ == '__main__':
    if len(sys.argv) > 1:
        arguments = sys.argv[1:]
        if arguments[0] == 'supports':
            backend = arguments[1]
            if does_support_backend(backend):
                sys.exit(0)
            else:
                sys.exit(1)

    context, book = json.load(sys.stdin)
    citations_config = context['config']['preprocessor']['citations']

    bib_database: pybtex.database.BibliographyData = pybtex.database.parse_file(citations_config.get('bibtex'))

    eprint("Bibliography read:", bib_database.to_string("yaml"))
    eprint("Citation", bib_database.entries["RSS20"])

    style_class = pybtex.plugin.find_plugin('pybtex.style.formatting', citations_config.get('citations_style'))
    style: pybtex.style.formatting.BaseStyle = style_class(label_style = pybtex.plugin.find_plugin('pybtex.style.labels', 'alpha'))
    # style.label_style = pybtex.plugin.find_plugin('pybtex.style.labels', 'alpha')

    # style = pybtex.style.formatting.alpha.AlphaStyle(label_style = pybtex.plugin.find_plugin('pybtex.style.labels', 'alpha'))

    backend: pybtex.backends.BaseBackend = pybtex.plugin.find_plugin('pybtex.backends', citations_config.get('backend_format'))()

    # Format the bibliography
    formatted_bibliography:pybtex.style.FormattedBibliography = style.format_bibliography(bib_database)


    output = io.StringIO()
    backend.write_to_stream(formatted_bibliography, output)
    html = output.getvalue()
    eprint(html)

    # eprint(formatted_bibliography.get_longest_label())
    # print(backend.render_sequence(formatted_bibliography))

    # Print the formatted citation
    for bibitem in formatted_bibliography:
        eprint(bibitem.label)


    if bool(citations_config.get('enable', True)) == True:
        book['sections'] = list(map(
            lambda s: process_citations_root_section(s, bib_database, style, backend),
            book['sections']))
    else:
        eprint('Skipping citation insertion, enable option was set to',
            citations_config.get('enable'))

    json.dump(book, sys.stdout)

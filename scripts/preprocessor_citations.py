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
DEFAULT_CITATION_STYLE = 'alpha'
DEFAULT_LABEL_CITATION_STYLE = 'alpha'

# Regex to match citation macros
CITE_REGEX = re.compile(r'\{\{#cite\s([^\}\s]+)(?:\s(.*))?\}\}')
NO_REF_CITE_REGEX = re.compile(r'(?<!-)\bno-ref\b(?!-)')
REFERENCE_REGEX = re.compile(r'\{\{#reference\s([^\}\s]+)(?:\s(.*))?\}\}')
BIBLIOGRAPHY_REGEX = re.compile(r'\{\{#bibliography(?:\s(.*))?\}\}')


def render_references(bib_database: pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle, backend: pybtex.backends.BaseBackend, cited_keys):
    formatted_bibliography = style.format_bibliography(
        bib_database, tuple(cited_keys))

    output = io.StringIO()
    backend.write_to_stream(formatted_bibliography, output)
    html = output.getvalue()

    for cite_key in cited_keys:
        cite_entry = bib_database.entries[cite_key]
        label = style.label_style.format_label(cite_entry)
        formatted_label = format_label(bib_database.entries[cite_key], style)
        html = html.replace(f'<dt>{label}</dt>', f'<dt class="reference-entry"><a name="reference-{
                            formatted_label}">&#91;{formatted_label}&#93;</a></dt>')

    html = html.replace("<body", "<body class='bibliography'")

    return html


def format_label(entry: pybtex.database.Entry, style: pybtex.style.formatting.BaseStyle):
    if CITEAS_FIELD in entry.fields.keys():
        return entry.fields[CITEAS_FIELD]
    else:
        return style.label_style.format_label(entry)


def format_citation(bib_database: pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle, match, cited_keys):
    cite_key = match.group(1)

    # Function to format the citation and collect cited keys
    if cite_key in bib_database.entries:
        if not match.group(2) or not NO_REF_CITE_REGEX.search(match.group(2)):
            cited_keys.add(cite_key)

        cite_entry = bib_database.entries[cite_key]

        formatted_label = format_label(cite_entry, style)

        return f'&#91;<a class="citation-link" href="#reference-{formatted_label}">{formatted_label}</a>&#93;'
    else:
        eprint(f"Warning: Citation key '{
               cite_key}' not found in bibliography.")
        return f'&#91;{cite_key}&#93;'


def generate_bibliography(bib_database: pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle, backend: pybtex.backends.BaseBackend, cited_keys):
    # Function to generate the bibliography section
    return render_references(bib_database, style, backend, cited_keys)


def process_citations_chapter_rec_mut(chapter, bib_database: pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle, backend):
    cited_keys = set()  # Set to keep track of all cited keys
    content = chapter.get('content', '')
    new_content = CITE_REGEX.sub(lambda match: format_citation(
        bib_database, style, match, cited_keys) or match.group(0), content)

    def sub_reference_regex_lambda(m):
        cite_key = m.group(1)
        if cite_key in bib_database.entries:
            cited_keys.add(cite_key)
            return ''
        else:
            eprint(f"Warning: Citation key '{
                cite_key}' was not found in the bibliography and will be ignored.")
            return m.group(0)

    new_content = REFERENCE_REGEX.sub(sub_reference_regex_lambda, new_content)

    if cited_keys:
        bibliography_section = generate_bibliography(
            bib_database, style, backend, cited_keys)
        if bibliography_section:
            new_content = insert_bibliography_at_correct_location(
                new_content, bibliography_section)

    chapter['content'] = new_content

    process_citations_sections_rec_mut(
        chapter['sub_items'], bib_database, style, backend)


def insert_bibliography_at_correct_location(content, bibliography_section):

    # Search for the placeholder in the content
    match = BIBLIOGRAPHY_REGEX.search(content)

    if match:
        # Replace the placeholder with the bibliography section
        new_content = BIBLIOGRAPHY_REGEX.sub(
            lambda _: bibliography_section, content)
    else:
        # If the placeholder isn't found, append the bibliography at the end of the content, with a `## References` header
        new_content = content + "\n\n## References\n\n" + bibliography_section

    return new_content


def process_citations_sections_rec_mut(sections, bib_database, style: pybtex.style.formatting.BaseStyle, backend: pybtex.backends.BaseBackend):
    for section in sections:
        chapter = section.get('Chapter')
        if chapter is None:
            continue

        process_citations_chapter_rec_mut(
            chapter, bib_database, style, backend)


def process_citations_root_section(section, bib_database: pybtex.database.BibliographyData, style: pybtex.style.formatting.BaseStyle, backend: pybtex.backends.BaseBackend):
    chapter = section.get('Chapter')
    if chapter is not None:
        process_citations_chapter_rec_mut(
            chapter, bib_database, style, backend)

    return section


def does_support_backend(backend):
    return backend == 'html' or backend == "linkcheck"


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

    if bool(citations_config.get('enable', True)):
        bib_database: pybtex.database.BibliographyData = pybtex.database.parse_file(
            citations_config.get('bibtex_file'))

        citation_style_config = citations_config.get(
            'citation_style', DEFAULT_CITATION_STYLE)
        style_class = pybtex.plugin.find_plugin(
            'pybtex.style.formatting', citation_style_config)

        label_style_str = citations_config.get(
            'citation_label_style', DEFAULT_LABEL_CITATION_STYLE)
        style: pybtex.style.formatting.BaseStyle = style_class(
            label_style=pybtex.plugin.find_plugin('pybtex.style.labels', label_style_str))

        backend: pybtex.backends.BaseBackend = \
            pybtex.plugin.find_plugin('pybtex.backends', 'html')()

        # The following must be run in order to detect errors in the .bib file
        formatted_bibliography: pybtex.style.FormattedBibliography = \
            style.format_bibliography(bib_database)
        output = io.StringIO()
        backend.write_to_stream(formatted_bibliography, output)
        # Optional: print to error stream
        # html = output.getvalue()
        # eprint(html)

        book['sections'] = list(map(
            lambda s: process_citations_root_section(
                s, bib_database, style, backend),
            book['sections']))
    else:
        eprint('Skipping citation insertion, enable option was set to',
               citations_config.get('enable'))

    json.dump(book, sys.stdout)
#!/usr/bin/env python3

# This file is intended to be used as a mdbook preprocessor,
# and it adheres to the appropriate protocol; see
# https://rust-lang.github.io/mdBook/for_developers/preprocessors.html#hooking-into-mdbook

import re
import pybtex
import pybtex.database
import pybtex.plugin
import pybtex.backends
import pybtex.backends.html
import pybtex.style.formatting
import pybtex.style.formatting.alpha
import pybtex.style.labels.alpha
import sys
import io
from utils import eprint
import json

# Defaults and other constants
CITEAS_FIELD = 'citeas'
DEFAULT_CITATION_STYLE = 'alpha'
DEFAULT_LABEL_CITATION_STYLE = 'custom_alpha'
DEFAULT_ERROR_ON_UNMATCHED_CITE_KEY = True
DEFAULT_ERROR_ON_EMPTY_BIBLIOGRAPHY = True

# Regex to match citation macros
CITE_REGEX = re.compile(r'\{\{#cite\s([^\}\s]+)(?:\s(.*))?\}\}')
# NO_REF_CITE_REGEX = re.compile(r'(?<!-)\bno-ref\b(?!-)')
REFERENCE_REGEX = re.compile(r'\{\{#reference\s([^\}\s]+)(?:\s(.*))?\}\}')
BIBLIOGRAPHY_REGEX = re.compile(r'\{\{#bibliography(?:\s(.*))?\}\}')


class CustomHtmlBackend(pybtex.backends.html.Backend):
    """
    Custom pybtex plugin for the html backend that formats the bibliography as a
    simple description list without formatting it as a complete HTML document.
    It also encases labels in square brackets, and adds css class attributes and
    anchors.
    """

    def write_prologue(self):
        self.output('\n\n<dl class="bibliography">\n')

    def write_epilogue(self):
        self.output('</dl>\n\n')

    def write_entry(self, key, label, text):
        self.output(f'<dt class="reference-entry"><a name="reference-{label}">&#91;{label}&#93;</a></dt>\n')
        self.output(f'<dd>{text}</dd>\n')


class CustomAlphaLabelStyle(pybtex.style.labels.alpha.LabelStyle):
    """
    Custom pybtex plugin for the alpha label style which overwrites it with the
    contents of the 'citeas' field of a bibliography entry if present.
    """

    def format_label(self, entry):
        if CITEAS_FIELD in entry.fields.keys():
            return entry.fields[CITEAS_FIELD]
        else:
            return super().format_label(entry)


# Register custom pybtex plugins
pybtex.plugin.register_plugin(
    'pybtex.backends', 'custom_html', CustomHtmlBackend)
pybtex.plugin.register_plugin(
    'pybtex.style.labels', 'custom_alpha', CustomAlphaLabelStyle)


def render_references(
        bib_database: pybtex.database.BibliographyData,
        style: pybtex.style.formatting.BaseStyle,
        backend: pybtex.backends.BaseBackend,
        cited_keys):
    formatted_bibliography = style.format_bibliography(
        bib_database, tuple(cited_keys))

    output = io.StringIO()
    backend.write_to_stream(formatted_bibliography, output)
    html = output.getvalue()

    return html


def format_citation(
        bib_database: pybtex.database.BibliographyData,
        style: pybtex.style.formatting.BaseStyle,
        match,
        cited_keys: set,
        unmatched_cite_keys: set,
        chapter):
    cite_key = match.group(1)

    # Function to format the citation and collect cited keys
    if cite_key in bib_database.entries:
        # if not match.group(2) or not NO_REF_CITE_REGEX.search(match.group(2)):
        cited_keys.add(cite_key)

        cite_entry = bib_database.entries[cite_key]

        formatted_label = style.label_style.format_label(cite_entry)

        return f'&#91;<a class="citation-link" href="#reference-{formatted_label}">{formatted_label}</a>&#93;'
    else:
        eprint(f"Error! Citation key '{cite_key}' used in #cite macro was not found in bibliography. File: '{chapter['path']}'")
        unmatched_cite_keys.add(cite_key)
        # If the cite_key is not recognized, we make the following guess about how to format the citation instead of failing completely
        return f'&#91;{cite_key}&#93;'


def generate_bibliography(
        bib_database: pybtex.database.BibliographyData,
        style: pybtex.style.formatting.BaseStyle,
        backend: pybtex.backends.BaseBackend,
        cited_keys):
    # Function to generate the bibliography section
    return render_references(bib_database, style, backend, cited_keys)


def process_citations_chapter_rec_mut(
        chapter,
        bib_database: pybtex.database.BibliographyData,
        style: pybtex.style.formatting.BaseStyle,
        backend,
        unmatched_cite_keys: set,
        empty_bibliography_invocations: set):
    cited_keys = set()  # Set to keep track of all cited keys
    content = chapter.get('content', '')
    new_content = CITE_REGEX.sub(lambda match: format_citation(
        bib_database, style, match, cited_keys, unmatched_cite_keys, chapter) or match.group(0), content)

    def sub_reference_regex_lambda(m):
        cite_key = m.group(1)
        if cite_key in bib_database.entries:
            cited_keys.add(cite_key)
            return ''
        else:
            eprint(f"Error! Citation key '{cite_key}' used in #reference macro was not found in bibliography. File: '{chapter['path']}'")
            unmatched_cite_keys.add(cite_key)
            return ''

    new_content = REFERENCE_REGEX.sub(sub_reference_regex_lambda, new_content)

    if cited_keys:
        bibliography_section = generate_bibliography(
            bib_database, style, backend, cited_keys)
        if bibliography_section:
            new_content = insert_bibliography_at_correct_location(
                new_content, bibliography_section)

    elif BIBLIOGRAPHY_REGEX.search(new_content):
        eprint(f"Error! A #bibliography macro was found, but there are no references. File: '{chapter['path']}'.")
        empty_bibliography_invocations.add(chapter['path'])

    chapter['content'] = new_content

    process_citations_sections_rec_mut(
        chapter['sub_items'], bib_database, style, backend, unmatched_cite_keys, empty_bibliography_invocations)


def insert_bibliography_at_correct_location(content, bibliography_section):

    # Search for the placeholder in the content
    match = BIBLIOGRAPHY_REGEX.search(content)

    if match:
        # Replace the placeholder with the bibliography section
        new_content = BIBLIOGRAPHY_REGEX.sub(
            lambda _: bibliography_section, content)
    else:
        # If the placeholder isn't found, append the bibliography at the end of the content, with a `## References` header
        new_content = content + '\n\n## References\n\n' + bibliography_section

    return new_content


def process_citations_sections_rec_mut(
        sections,
        bib_database,
        style: pybtex.style.formatting.BaseStyle,
        backend: pybtex.backends.BaseBackend,
        unmatched_cite_keys: set,
        empty_bibliography_invocations: set):
    for section in sections:
        chapter = section.get('Chapter')
        if chapter is None:
            continue

        process_citations_chapter_rec_mut(
            chapter, bib_database, style, backend, unmatched_cite_keys, empty_bibliography_invocations)


def process_citations_root_section(
        section,
        bib_database: pybtex.database.BibliographyData,
        style: pybtex.style.formatting.BaseStyle,
        backend: pybtex.backends.BaseBackend,
        unmatched_cite_keys: set,
        empty_bibliography_invocations: set):
    chapter = section.get('Chapter')
    if chapter is not None:
        process_citations_chapter_rec_mut(
            chapter, bib_database, style, backend, unmatched_cite_keys, empty_bibliography_invocations)

    return section


def does_support_backend(backend):
    return backend == 'html' or backend == 'linkcheck'


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

    unmatched_cite_keys = set()
    empty_bibliography_invocations = set()

    if bool(citations_config.get('enable', True)):
        bib_database: pybtex.database.BibliographyData = pybtex.database.parse_file(
            citations_config.get('bibtex-file'))

        # Config
        citation_style_config = citations_config.get(
            'citation-style', DEFAULT_CITATION_STYLE)
        label_style_config = citations_config.get(
            'citation-label-style', DEFAULT_LABEL_CITATION_STYLE)
        backend_config = 'custom_html'

        # Initialize pybtex classes
        style_class = pybtex.plugin.find_plugin(
            'pybtex.style.formatting', citation_style_config)
        style: pybtex.style.formatting.BaseStyle = style_class(
            label_style=pybtex.plugin.find_plugin('pybtex.style.labels', label_style_config))
        backend: pybtex.backends.BaseBackend = pybtex.plugin.find_plugin(
            'pybtex.backends', backend_config)()

        # The following must be run in order to detect errors and missing fields in the bibtex file
        formatted_bibliography: pybtex.style.FormattedBibliography = \
            style.format_bibliography(bib_database)
        # # Optional: print to error stream
        # output = io.StringIO()
        # backend.write_to_stream(formatted_bibliography, output)
        # html = output.getvalue()
        # eprint(html)

        book['sections'] = list(map(
            lambda s: process_citations_root_section(
                s, bib_database, style, backend, unmatched_cite_keys, empty_bibliography_invocations),
            book['sections']))
    else:
        eprint('Skipping citation insertion, enable option was set to',
               citations_config.get('enable'))

    json.dump(book, sys.stdout)

    if unmatched_cite_keys:
        eprint('The following unmatched bibliography keys were found while processing citations: ', ', '.join(sorted(unmatched_cite_keys)))

        if citations_config.get('error-on-unmatched-keys', DEFAULT_ERROR_ON_UNMATCHED_CITE_KEY):
            sys.exit(1)

    if empty_bibliography_invocations:
        eprint('The following files have #bibliography macro invocations with empty bibliographies: ', ', '.join(sorted(empty_bibliography_invocations)))

        if citations_config.get('error-on-empty-bibliography', DEFAULT_ERROR_ON_EMPTY_BIBLIOGRAPHY):
            sys.exit(2)

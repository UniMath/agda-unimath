#!/usr/bin/env python3

from collections import defaultdict
import re

# In mdbook-catppuccin this is merged to catppuccin.css, so we'll need
# to update this script accordingly
CATPPUCCIN_HIGHLIGHT_FILE = 'theme/catppuccin-highlight.css'
AGDA_HIGHLIGHT_FILE = 'website/css/Agda-highlight.css'

# First group -> theme name
# Second group -> token class
SELECTOR_HLJS_REGEX = re.compile(r'^\.(\w+) code \.hljs-(.+?) {')

# First group -> theme name
SELECTOR_CODE_REGEX = re.compile(r'^\.(\w+) code {')

# Description of hljs classes taken from here:
# - https://highlightjs.readthedocs.io/en/latest/css-classes-reference.html
# Description of Agda classes taken from here:
# - https://agda.github.io/agda/Agda-Syntax-Common-Aspect.html
# Matching between the two:
# - revealed to me in a dream
CLASSES_MAP = defaultdict(list)

# Aspects
CLASSES_MAP['comment'].append('Comment')
# CLASSES_MAP[''].append('Markup')
CLASSES_MAP['keyword'].append('Keyword')
CLASSES_MAP['string'].append('String')
CLASSES_MAP['number'].append('Number')
CLASSES_MAP['punctuation'].append('Symbol')
CLASSES_MAP['built_in'].append('PrimitiveType')
# CLASSES_MAP[''].append('Pragma')
CLASSES_MAP['operator'].append('Operator')
# CLASSES_MAP[''].append('Hole')

# NameKinds
CLASSES_MAP['variable'].append('Bound')
# CLASSES_MAP[''].append('Generalizable')
CLASSES_MAP['title.function_'].append('InductiveConstructor')
CLASSES_MAP['title.class_'].append('CoinductiveConstructor')
CLASSES_MAP['type'].append('Datatype')
CLASSES_MAP['property'].append('Field')
CLASSES_MAP['title.function_'].append('Function')
CLASSES_MAP['variable.constant_'].append('Module')
CLASSES_MAP['literal'].append('Postulate')
CLASSES_MAP['literal'].append('Primitive')
# Use the same color as modules
CLASSES_MAP['title.function_'].append('Record')

# OtherAspects
# Keep the defaults, they should be legible on all themes
# CLASSES_MAP[''].append('DottedPattern')
# CLASSES_MAP[''].append('UnsolvedMeta')
# CLASSES_MAP[''].append('UnsolvedConstraint')
# CLASSES_MAP[''].append('TermintaionProblem')
# CLASSES_MAP[''].append('IncompletePattern')
# CLASSES_MAP[''].append('Error')
# CLASSES_MAP[''].append('TypeChecks')
# CLASSES_MAP[''].append('Deadcode')
# CLASSES_MAP[''].append('ShadowingInTelescope')


def dump_block_for_themes(theme, classes, contents, outfile, is_selector_class=True):
    themes = [theme]
    if theme == 'mocha':
        themes += ['coal', 'navy', 'ayu']
    for theme in themes:
        for agda_class in classes:
            print(
                f'.{theme} pre.Agda {is_selector_class * "."}{agda_class} {{\n{contents}}}\n',
                file=outfile
            )
        pass


if __name__ == '__main__':
    with open(CATPPUCCIN_HIGHLIGHT_FILE) as highlight_css:
        with open(AGDA_HIGHLIGHT_FILE, 'w') as agda_highlight_css:
            scan_current_theme = ''
            scan_current_class = ''
            scan_current_contents = ''
            for line in highlight_css:
                # line = line.strip()
                selector_hljs_match = SELECTOR_HLJS_REGEX.match(line)
                # Push stanza
                if selector_hljs_match:
                    scan_current_theme = selector_hljs_match.group(1)
                    scan_current_class = selector_hljs_match.group(2)
                    continue
                selector_code_match = SELECTOR_CODE_REGEX.match(line)
                if selector_code_match:
                    scan_current_theme = selector_code_match.group(1)
                    scan_current_class = 'code-block'
                    continue
                # Ignore unrecognized blocks
                if line.startswith('.'):
                    scan_current_theme = ''
                    scan_current_class = ''
                # Pop stanza, flush contents
                if line.startswith('}'):
                    if scan_current_class == 'code-block':
                        dump_block_for_themes(
                            scan_current_theme, [''],
                            scan_current_contents,
                            agda_highlight_css,
                            is_selector_class=False)

                    agda_classes = CLASSES_MAP.get(scan_current_class)
                    if not scan_current_class == '' and agda_classes:
                        dump_block_for_themes(
                            scan_current_theme,
                            agda_classes,
                            scan_current_contents,
                            agda_highlight_css)
                    scan_current_contents = ''
                    continue
                # Collect contents
                scan_current_contents += line

#!/usr/bin/env python3
# Run this script:
# $ ./scripts/generate_namespace_index_modules.py

# * Remember to update the script's entry in `CONTRIBUTING.md` on changes

import pathlib
import sys
import utils


def generate_title(namespace):
    return '# ' + namespace.capitalize().replace('-', ' ') + '\n'


def generate_imports(root, namespace, git_tracked_files):
    namespace_path = root.joinpath(namespace)
    namespace_files = [
        f.name for f in namespace_path.iterdir() if utils.is_agda_file(f) and f in git_tracked_files]

    import_statements = [utils.get_import_statement(
        namespace, module_file, public=True) for module_file in namespace_files]
    return '\n'.join(sorted(set(import_statements)))


agda_block_template = \
    '''```agda
module {namespace} where

{imports}
```
'''


def generate_agda_block(root, namespace, git_tracked_files):
    return agda_block_template.format(namespace=namespace, imports=generate_imports(root, namespace, git_tracked_files))


if __name__ == '__main__':
    CHANGES_WERE_MADE_FLAG = 1
    MISPLACED_TITLE_FLAG = 2
    status = 0
    root = pathlib.Path('src')

    git_tracked_files = set(utils.get_git_tracked_files())

    for namespace in utils.get_subdirectories_recursive(root):
        if namespace == 'temp' or 'MAlonzo' in namespace:
            continue

        namespace_filename = root.joinpath(namespace).with_suffix('.lagda.md')

        if namespace_filename.is_file():
            with namespace_filename.open('r+') as namespace_file:
                contents = namespace_file.read()
        else:
            contents = ''

        oldcontents = contents

        title_index = contents.find('# ')
        if title_index > 0:
            print(
                f'Warning! Namespace file {namespace_filename} should start with a top-level title.', file=sys.stderr)
            status |= MISPLACED_TITLE_FLAG
        elif title_index == -1:  # Missing title, generate it
            contents = generate_title(namespace) + contents

        agda_block_start = contents.rfind('```agda\n')

        if agda_block_start == -1:
            # Must add agda block
            # Add at the end of the file
            contents += '\n' + \
                generate_agda_block(root, namespace, git_tracked_files)
        else:
            agda_block_end = contents.find(
                '\n```\n', agda_block_start + len('```agda\n'))
            generated_block = generate_agda_block(
                root, namespace, git_tracked_files)

            if agda_block_end == -1:
                # An agda block is opened but not closed.
                # This is an error, but we can fix it
                print(
                    f'WARNING! agda-block was opened but not closed in {namespace_filename}.', file=sys.stderr)
                contents = contents[:agda_block_start] + generated_block
            else:
                agda_block_end += len('\n```\n')
                contents = contents[:agda_block_start] + \
                    generated_block + contents[agda_block_end:]

        if oldcontents != contents:
            status |= CHANGES_WERE_MADE_FLAG
            with namespace_filename.open('w') as f:
                f.write(contents)

    sys.exit(status)

#!/usr/bin/env python3
# Run this script:
# $ ./scripts/generate_contributors.py

import subprocess
from utils.contributors import parse_contributors_file, sorted_authors_from_raw_shortlog_lines


template = """
## Contributors

We are grateful to the following people for their contributions to
the library.

{names}

Help us to improve the library by contributing to the project!
Contributions come in many forms, please ask us if you are not sure
how to help. We are happy to help you get started.
"""

def github_page_for_username(username):
    return f'https://github.com/{username}'

def format_contributor(contributor):
    display_name = contributor['displayName']
    github_username = contributor.get('github')
    if github_username:
        return f'- [{display_name}]({github_page_for_username(github_username)})'
    return f'- {display_name}'

if __name__ == '__main__':
    contributors_data = parse_contributors_file()

    git_log_output = subprocess.run([
        'git', 'shortlog',
        '-ns',
        '--invert-grep', '--grep=^chore:',
        '--group=author', '--group=trailer:co-authored-by',
        'HEAD'
    ], capture_output=True, text=True, check=True).stdout.splitlines()

    sorted_authors = sorted_authors_from_raw_shortlog_lines(git_log_output, contributors_data)
    output = template.format(names='\n'.join((format_contributor(c) for c in sorted_authors)))

    with open('CONTRIBUTORS.md', 'w') as output_file:
        output_file.write(output)

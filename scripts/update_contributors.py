#!/usr/bin/env python3
# Run this script:
# $ ./scripts/update_contributors.py

import requests
import sys
import json

s = requests.Session()
s.trust_env = False

repo = 'unimath/agda-unimath'
url = f'https://api.github.com/repos/{repo}/contributors'

response = s.get(url)

if response.status_code != 200:
    print(f'Failed to retrieve contributors for repository {repo}. '
          f'Status code: {response.status_code}', file=sys.stderr)
    exit(1)

contributors = json.loads(response.text)


template = """
## Contributors

We are grateful to the following people for their contributions to
the library.

{names}

Help us to improve the library by contributing to the project!
Contributions come in many forms, please ask us if you are not sure
how to help. We are happy to help you get started.
"""


def get_github_user_name(username):
    url = f'https://api.github.com/users/{username}'

    response = s.get(url)

    if response.status_code != 200:
        print(f'Failed to retrieve information for user {username}. '
              f'Status code: {response.status_code}', file=sys.stderr)
        return ''

    user_info = json.loads(response.text)

    name = user_info.get('name', '')

    return name


contributors_list = []

for contributor in contributors:
    login = contributor['login']
    html_url = contributor['html_url']
    name = get_github_user_name(login)
    if name is None or name == '':
        name = login
    contributors_list.append(f'- [{name}]({html_url})')

output = template.format(names='\n'.join(contributors_list))

with open('CONTRIBUTORS.md', 'w') as file:
    file.write(output)

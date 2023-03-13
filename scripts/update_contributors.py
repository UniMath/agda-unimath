import requests
import json

repo = "unimath/agda-unimath"
url = f"https://api.github.com/repos/{repo}/contributors"

response = requests.get(url)

if response.status_code != 200:
    print(f"Failed to retrieve contributors for repository {repo}. "
          f"Status code: {response.status_code}")
    exit(1)

contributors = json.loads(response.text)

sorted_contributors = sorted(contributors, key=lambda c: c['login'])

template = """
## Contributors

We are grateful to the following people for their contributions to
the library. In alphabetical order, by GitHub username:

Name 1

Help us to improve the library by contributing to the project!
Contributions come in many forms, please ask us if you are not sure
how to help. We are happy to help you get started.
"""

def get_github_user_name(username):
    url = f"https://api.github.com/users/{username}"

    response = requests.get(url)

    if response.status_code != 200:
        print(f"Failed to retrieve information for user {username}. "
              f"Status code: {response.status_code}")
        return ""

    user_info = json.loads(response.text)

    name = user_info.get('name', '')

    return name

contributors_list = []

for contributor in sorted_contributors:
    login = contributor['login']
    name = get_github_user_name(login)
    if name is None or name == "":
        name = login
    html_url = contributor['html_url']
    contributors_list.append(f"- [{name} ({login})]({html_url})")

output = template.replace("Name 1", "\n".join(contributors_list))

with open("CONTRIBUTORS.md", "w") as file:
    file.write(output)

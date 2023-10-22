from collections import defaultdict
import sys
import tomli

CONTRIBUTORS_FILE = 'CONTRIBUTORS.toml'


def format_multiple_authors_attribution(author_names):
    return ', '.join(
        author_names[:-1]) + (len(author_names) > 1) * ' and ' + author_names[-1]


def parse_contributors_file(path=CONTRIBUTORS_FILE):
    with open(path, 'rb') as f:
        return tomli.load(f)['contributors']


def print_skipping_contributor_warning(contributor):
    print('Warning: not attributing changes to', contributor,
          f'. If you want your work to be attributed to you, add yourself to {CONTRIBUTORS_FILE}',
          file=sys.stderr)


def get_real_author_index(raw_username, contributors):
    return next((index for (index, c) in enumerate(contributors) if raw_username in c['usernames']), None)


def sorted_authors_from_raw_shortlog_lines(shortlog, contributors):
    author_commits = defaultdict(int)
    for raw_author_line in shortlog:
        commit_count_str, raw_author = raw_author_line.split('\t')
        commit_count = int(commit_count_str.strip())
        author_index = get_real_author_index(raw_author, contributors)
        if author_index is None:
            print_skipping_contributor_warning(raw_author)
            continue
        author_commits[author_index] += commit_count
    sorted_author_indices = sorted(
        author_commits, key=author_commits.get, reverse=True)
    return [contributors[author_index] for author_index in sorted_author_indices]

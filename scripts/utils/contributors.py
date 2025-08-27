from collections import defaultdict
import sys
import tomli


def format_multiple_authors_attribution(author_names):
    return ', '.join(
        author_names[:-1]) + (len(author_names) > 1) * ' and ' + author_names[-1]


def parse_contributors_file(contributors_file):
    with open(contributors_file, 'rb') as f:
        return tomli.load(f)['contributors']


def print_skipping_contributor_warning(contributor, contributors_file):
    print('Warning: not attributing changes to', contributor,
          f'. If you want your work to be attributed to you, add yourself to {contributors_file}',
          file=sys.stderr)


def get_real_author_index(raw_username, contributors):
    return next((index for (index, c) in enumerate(contributors) if raw_username in c['usernames']), None)


def sorted_authors_from_raw_shortlog_lines(shortlog, contributors, contributors_file):
    author_commits = defaultdict(int)
    for raw_author_line in shortlog:
        commit_count_str, raw_author = raw_author_line.split('\t')
        commit_count = int(commit_count_str.strip())
        author_index = get_real_author_index(raw_author, contributors)
        if author_index is None:
            print_skipping_contributor_warning(raw_author, contributors_file)
            continue
        author_commits[author_index] += commit_count
    sorted_author_indices = sorted(
        author_commits, key=author_commits.get, reverse=True)
    return [contributors[author_index] for author_index in sorted_author_indices]

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
    print(f'Warning: not attributing changes to {contributor}. If you want your work to be attributed to you, add yourself to {contributors_file}.',
          file=sys.stderr)


def print_skipping_contributors_warning(contributors, contributors_file):
    for contributor in sorted(contributors):
        print_skipping_contributor_warning(contributor, contributors_file)


def get_real_author_index(raw_username, contributors):
    return next((index for (index, c) in enumerate(contributors) if raw_username in c['usernames']), None)


def sorted_authors_from_raw_shortlog_lines(shortlog, contributors):
    author_commits = defaultdict(int)
    skipped_authors = set()
    for raw_author_line in shortlog:
        commit_count_str, raw_author = raw_author_line.split('\t')
        commit_count = int(commit_count_str.strip())
        author_index = get_real_author_index(raw_author, contributors)
        if author_index is None:
            skipped_authors.add(raw_author)
            continue
        author_commits[author_index] += commit_count
    # for raw_author in sorted(skipped_authors):
    #     print_skipping_contributor_warning(raw_author, contributors_file)
    sorted_author_indices = sorted(
        author_commits, key=author_commits.get, reverse=True)
    return [contributors[author_index] for author_index in sorted_author_indices], skipped_authors

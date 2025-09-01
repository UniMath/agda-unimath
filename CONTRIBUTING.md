# Contributing to the library

We employ several tools to maintain our library. This guide will walk you
through their usage and help ensure your contributions meet our standards.

## The `make pre-commit` tool

The `make pre-commit` tool checks library conventions and performs basic tasks.
Our installation instructions for the `make pre-commit` tool can be found
[here](HOWTO-INSTALL.md#contributor-setup).

Before you run the tool, ensure that your files are properly tracked by git by
staging any relevant file additions or deletions. This is what the commands
`git add <path-to-new-file>` and `git add <path-to-deleted-file>` do
respectively.

The `make pre-commit` tool can generate errors during the first run while
correcting some of them automatically. If all goes well, the second run should
pass all checks and initiate the verification of the entire library via
`make check`.

Below is a summary of the tasks this tool performs:

- **Trailing whitespace**: Identifies and removes any trailing whitespace.

- **End of files**: Ensures that a file is either empty, or ends with one new
  line.

- **Mixed line ending**: Ensures consistent use of line endings
  ([LF vs CRLF](https://www.aleksandrhovhannisyan.com/blog/crlf-vs-lf-normalizing-line-endings-in-git/#crlf-vs-lf-what-are-line-endings-anyway)).

<!--
- **Double quoted strings**: Replaces double quoted strings with single quoted
  strings.
-->

- **Python AST**: Checks whether Python scripts parse as valid Python.

- **YAML**: Checks yaml files for parseable syntax.

- **Spellcheck with codespell**: Checks for spelling mistakes with the
  [codespell](https://github.com/codespell-project/codespell) tool. This is a
  permissible spellchecker that only reports known misspellings, rather than
  words it does not recognize. I.e., it is a blacklist based spellchecker. We
  maintain an additional library-defined dictionary of misspellings at:
  [`config/codespell-dictionary.txt`](https://github.com/UniMath/agda-unimath/blob/master/codespell-dictionary.txt).
  If you find a misspelled word in the library, it is good practice to add it to
  this dictionary in addition to correcting the mistake. If codespell
  erroneously reports a word as misspelled, please add it to
  [`config/codespell-ignore.txt`](https://github.com/UniMath/agda-unimath/blob/master/codespell-ignore.txt).

- **Sort codespell dictionary and ignore files**: Sorts and formats the
  associated codespell dictionary and ignore files.

- **Case conflicts**: Checks for files that would conflict in case-insensitive
  filesystems.

- **Merge conflicts**: Checks for any merge conflict artifacts in the code.

- **Markdown conventions**: Checks/enforces various of our conventions related
  to markdown code. This includes removing punctuation in section headers,
  removing empty code blocks, ensuring that there is only one top-level header
  and that this is placed on the first line of the file, checking that no
  section is void of contents, checking that headings don't contain links, and
  checking that file names consist only of ASCII characters.

- **Blank line conventions**: Searches for and removes any double or multiple
  blank lines.

- **Agda space conventions**: Corrects some common spacing mistakes according to
  our conventions. This includes removing repeat whitespace characters between
  two non-whitespace characters in a line, having whitespace before an opening
  brace or semicolon if it is not preceded by a dot or another opening brace,
  and having whitespace after a closing brace or semicolon if it is not
  succeeded by a closing brace.

- **Indentation conventions**: Verifies that the indentation level is always a
  multiple of two. If inconsistencies are found, it provides an error report
  indicating the location of the issues.

- **Wrap long lines**: Scans for any lines exceeding the 80-character limit that
  can be resolved by simple rules for inserting line breaks. It inserts line
  breaks at the beginning of any definition, but not in the middle of a
  definition.

- **Maximum line length**: Detects any violations of the 80-character line limit
  and reports them. Note that single tokens such as long names can exceed this
  limit.

- **Generate namespace indexes of modules**: Generates and maintains the indexes
  of modules for each folder in `src`. For example, the `group-theory/` folder
  has a corresponding `src/group-theory.lagda.md` file that imports all the
  modules in `group-theory/` publicly. You do not need to maintain these files
  manually, although they can be edited.

**Note**: The previous two hooks only detect tracked files. This means that if
you add or delete files, they must be staged for these hooks to take these
changes into consideration. This gives you finer control over your commits. For
instance, if a file is not ready to be committed, you can still use the
pre-commit tool and just not stage that file.

<!--
- **Python scripts formatting**: Performs `autopep8` formatting on Python
  scripts. Note that this script takes care of most formatting for Python
  scripts, so you should not worry about formatting them.
-->

- **CSS, JS, YAML and Markdown (no codeblocks) formatting**: Performs basic
  formatting tasks such as enforcing the 80-character line limit, formatting
  markdown tables, among others. Note that this script takes care of all
  formatting for these file types, so you should not worry about formatting such
  files.

- **BibTeX formatting:** Formats the
  [`references.bib`](https://github.com/UniMath/agda-unimath/blob/master/references.bib)
  file using [`bibtex-tidy`](https://github.com/FlamingTempura/bibtex-tidy).

## The `make website` tool

After you complete the `make pre-commit` process, you can run `make website` to
verify that the current changes will not interfere with the website's
compilation. This tool starts by running `make check` and then builds the
website, reporting any broken internal links that may prevent the website build
from completing.

Installation instructions for the `make website` tool can be found
[here](HOWTO-INSTALL.md#contributor-setup).

## Adding yourself as a contributor {#add-contributor}

When you submit changes to the library, you have every right to call yourself a
contributor. We can attribute your work to you by listing your preferred name on
our [list of contributors](CONTRIBUTORS.md), and by including your name on the
source pages you helped create.

This attribution process is automated, so all you need to do is add a section to
the `CONTRIBUTORS.toml` file, where you can customize how you appear on the
website. If you do not want to be mentioned on the website, simply leave
yourself out of this file. For most contributors, the new section will look like
the following:

```toml
[[contributors]]
displayName = "Vojtěch Štěpančík"
usernames = [ "Vojtěch Štěpančík", "VojtechStep" ]
github = "VojtechStep"
```

The `displayName` field tells our tooling how to display your name - be it on
the Contributors page, the source page headers, or in the list of recent
changes. The `github` field is optional, and when included it makes you name on
the Contributors page into a link to your GitHub profile.

The `usernames` list is very important - that's how you tell the build process
which commits belong to you. Because of some peculiarities with GitHub's
handling of author and co-author information, this list will very often include
two names: your local git username, which you can get by running
`git config user.name` from the command-line in your local clone of the
repository; and your GitHub _display name_, which you can get by navigating to
your user profile on GitHub, where it's the one directly under your profile
picture. If you change your GitHub display name, the old commits will still use
the old name, but your new changes will use the new name, so if you keep
contributing to the library, you'll need to add that new name to the list. If
you have any doubts or questions, feel free to reach out on the
[Discord server](https://discord.gg/Zp2e8hYsuX) or in the comments of your pull
request.

Additional fields you can add are all optional strings, and they are `extra`,
`homepage` and `bio`. Currently they have no effect on how your information is
displayed on the website.

## Submitting your pull request on GitHub

Once all checks are passed, you're ready to submit your pull request. Please
provide a brief description of the significant changes you made. Keep in mind
that the individual commits in your pull request will be squashed into a single
commit, and its commit message will be the description you provide in your pull
request.

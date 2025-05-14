# Self-review and merge guidelines

## Purpose

This document outlines the process for maintainers to perform self-reviews and
merge pull requests without a second maintainer's review. The goal is to
maintain high-quality contributions while enabling progress when maintainers
have limited availability.

## When self-review is appropriate

Self-review and merge is appropriate for maintainers under the following
conditions:

- The PR has been open for at least 3 weeks
- No maintainer has had time to review the PR
- The changes follow established practices and don't introduce novel library
  approaches

**Note:** Self-review is only appropriate for maintainers. PRs from regular
contributors should still undergo review by at least one maintainer.

## Required waiting period

1. Submit your PR and request reviews from other maintainers
2. Wait for at least 3 weeks from the last substantive change to the PR
3. If no review has been provided after sending reminders, proceed with
   self-review

This waiting period serves two purposes:

- It provides a grace period for others to review and give input
- It allows you to look at your code with fresh eyes before performing the
  self-review

## Self-review checklist

Before merging your own PR, make sure to review each of the following aspects:

### Mathematical correctness

- [ ] Mathematical statements are correct
- [ ] Terminology is consistent with established literature
- [ ] For concepts not appearing in literature, disclaimers have been added
- [ ] Claims without accompanying formalization include appropriate citations
- [ ] Changes to existing content are uncontroversial and well-justified

### Documentation

- [ ] All new terms are clearly defined
- [ ] Documentation is clear and accessible
- [ ] Citations are provided when introducing new terminology
- [ ] You can confidently say: "I will understand this paragraph in a year"

### Content quality

- [ ] Content follows the library's conventions as outlined in
  - [Design principles](DESIGN-PRINCIPLES.md)
  - [Coding style](CODINGSTYLE.md)
  - [File conventions](FILE-CONVENTIONS.md)
  - [Guidelines for mixfix operators](MIXFIX-OPERATORS.md)
  - [Citing sources](CITING-SOURCES.md)
- [ ] No duplication with existing content

## Seeking assistance

If you have questions during the self-review process:

1. For quick questions, ask in the project Discord or message the other
   maintainers
2. For more complex issues, consider creating an issue on GitHub
3. Don't wait indefinitely for responses; use your best judgment if responses
   are not forthcoming
4. Document significant decisions in your PR description

## Final merge requirements

Before merging your PR:

1. Complete and document the self-review process in the PR
2. State that you're merging under the self-review policy after the 3-week
   waiting period
3. Be prepared to address any issues discovered after merging

## Continuous improvement

Remember that the ultimate goal is to maintain high-quality contributions while
enabling the project to progress despite limited reviewer availability.

# Citing sources

All of the references and sources of the agda-unimath library are managed in a
[BibLaTeX](https://www.ctan.org/pkg/biblatex) file `references.bib`, and we have
a custom set of macros to work with them.

The three macros are as follows:

- `{{#cite labelXYZ}}` will insert a citation to the reference labeled
  `labelXYZ` (which must be defined in the `references.bib` file) at the current
  location, and add that reference to the current page's bibliography.
- `{{#reference labelXYZ}}` will add the reference labeled `labelXYZ` to the
  current page's bibliography without inserting a citation.
- `{{#bibliography}}` is a marker for where the bibliography of the current page
  should be inserted. If no such marker is found and the bibliography is
  inhabited, it will be inserted at the bottom of the page in a new section
  titled `References`.

Note that entries in the BibLaTeX file are expected to have all of the
apropriate fields defined according to their type. For instance, `@book`s _must_
have a defined field for `publisher` and `year`. If this information is not
available, please define them as empty fields. E.g. `publisher = {},`.

If you are unsure about how to structure your BibLaTeX entry, it may be useful
to know that the references are checked by the `linkcheck` GitHub workflow, so
when you post your pull request to `agda-unimath` you can refer to the CI for
possible issues.

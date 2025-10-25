# Citing sources

All of the references and sources of the agda-unimath library are managed in a
[BibLaTeX](https://www.ctan.org/pkg/biblatex) file
[`references.bib`](https://github.com/UniMath/agda-unimath/blob/master/references.bib),
and we have a custom set of macros to work with them.

The macros are as follows:

<!--
We have inserted an invisible whitespace character between the first and second
opening curly braces in the below examples to block the citation preprocessor
from detecting them as macros.
-->

- `{­{#cite referenceXYZ}}` will insert a citation to the reference labeled
  `referenceXYZ` (which must be defined in the `references.bib` file) at the
  current location, and add that reference to the current page's bibliography.
- `{­{#reference referenceXYZ}}` will add the reference labeled `referenceXYZ`
  to the current page's bibliography without inserting a citation.
- `{­{#bibliography}}` is a marker for where the bibliography of the current
  page should be inserted. If no such marker is found and the bibliography is
  inhabited, it will be inserted at the bottom of the page in a new section
  titled `References`. However, this feature of the preprocessor is still
  experimental, and a better positioning of the `References` section is achieved
  by manually inserting it.

Note that entries in the BibLaTeX file are expected to have all of the
appropriate fields defined according to their type. For instance, `@book`s
_must_ have a defined field for `publisher` and `year`. If this information is
not available, please define them as empty fields. E.g. `publisher = {},`.

If you are unsure about how to structure your BibLaTeX entry, it may be useful
to know that the references are checked by the `linkcheck` GitHub workflow, so
when you post your pull request to the agda-unimath repository you can refer to
the CI for possible issues.

**Note:** If the citation label of your reference is not being generated
properly, we support a custom `citeas` field that overwrites it. For instance,
_Homotopy Type Theory: Univalent Foundations of Mathematics_ should be cited as
{{#cite UF13}}, and to make it so we have set `citeas = {UF13}` for its BibLaTeX
entry. Keep in mind that if the citation label is not being generated properly,
then it is likely that the author list is not being parsed properly either.

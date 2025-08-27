# Style conventions for files

This document outlines the style conventions for files in the library. These
conventions are based on the [design principles](DESIGN-PRINCIPLES.md) of the
library.

## General conventions

### File names should be descriptive

File names should be descriptive of the concept it introduces or the main
theorem proven. The file names could be considered indexing terms, with the list
of files functioning much like the index in the back of a book. Usually, file
names consist of a noun or a noun phrase. File names should be natural,
sufficiently precise, concise, and consistent with those of related files.
Additionally, prepositions are usually included in the file name. E.g.
`fibers-of-maps` as opposed to `fibers-maps`.

### File names are all lowercase with words separated by hyphens

File names should be entirely in lowercase, with words separated by hyphens.
Avoid abbreviating words in file names unless the abbreviated term is a widely
accepted mathematical term, such as `poset`.

### The file format is literate Agda with markdown

Files that are part of the formalization should be in literate Agda using
markdown. The file extension is `.lagda.md`.

### File header and module declaration

Every file should begin with a header in the following format:

```md
# The title of the file
```

Note that the title of the file and other markdown headers must be on one line,
even if it contains more than 80 characters. Headers that exceed the 80
character limit are not considered violations of the 80 character rule.

Directly after the header, include an Agda code block containing

- any option pragmas,
- the main module declaration,
- any public import statements

in this order. E.g.

````md
```agda
{-# OPTIONS ... #-}

module ... where

open import ... public
```
````

### Imports block

After the module declaration, include an Agda code block of all nonpublic module
imports starting with `<details><summary>Imports</summary>` and ending with
`</details>`. This block should only contain module imports and there should
have no further import statements after it. In the rendered markdown, the
contents of this block will be hidden by default, but can be revealed by
clicking on _Imports_.

````md
<details><summary>Imports</summary>

```agda
open import ...
```

</details>
````

### Sections and headings

Organize the rest of the file into sections, subsections, and possibly
subsubsections. Use `##` headings for the main sections of the file and reserve
`#` headings only for the title of the file. Common sections include `## Idea`,
`## Definitions`, and `## Properties`. Occasionally, you might include a section
like `## Examples` or `## Theorem`, based on the purpose of the file.

Ideally, depending on the purpose of the file, the first section explains the
main idea, the second section proceeds to give the main definition that is the
focus of the file, then the third section proceeds possibly with basic
properties of the defined concept. In rare cases we also have an example
section, but often it is better to cover examples in their own files and
referencing those in the `See also` section.

In the `Idea` section, the main idea behind the topic of the current file must
be explained. In this short, informal section we display the defined concept in
bold, i.e., using `**defined concept**` and any technical terms that are used in
this explanation are hyperlinked to other pages in the library. For example, the
`Idea` section of
[Galois connections on large posets](order-theory.galois-connections-large-posets.md)
looks in markdown as follows:

````md
## Idea

A **galois connection** between [large posets](order-theory.large-posets.md) `P`
and `Q` consists of
[order preserving maps](order-theory.order-preserving-maps-large-posets.md)
`f : hom-Large-Poset id P Q` and `hom-Large-Poset id Q P` such that the adjoint
relation

```text
  (f x ≤ y) ↔ (x ≤ g y)
```

holds for every two elements `x : P` and `y : Q`.
````

Note that section and subsection headers must be on one line, even if they
contain more than 80 characters. Headers that exceed the 80 character limit are
not considered violations of the 80 character rule.

### Subsections

Use `###` headings for subsections within the main sections. If a code block
following a heading is very long, you can use `####` headings to subdivide the
subsections further. Ensure that subsection headings concisely describe the
content of the following code block. However, don't hesitate to include
explanatory text within a section when necessary.

### Tables

If you want to include a table in your file, for example listing examples of a
relevant construction or files with related concepts, we suggest adding the
table as its own Markdown file in the `docs/tables` directory, using
[Markdown syntax for tables](https://www.markdownguide.org/extended-syntax/#tables).
This isn't a strict rule, and there are valid reasons for only having a table in
a file directly, but for the two example cases outlined above, we recommend
maintaining the table separately. The file should contain only the table and it
should have a descriptive name. It can then be included with the mdbook
`{{#include}}` directive, as in the following example:

```md
## Examples of categories and large categories

\{{#include tables/categories.md}}
```

All tables are formatted automatically by a pre-commit script, so you don't need
to worry about properly aligning everything - as long as the Markdown parser
recognizes it as a table, running `make pre-commit` will change it to its
canonical text representation.

### See also and references

At the end of the file you may add a `See also` or `References` subsection where
you reference related sources such as other modules or articles related to the
contents of the file.

- You can reference another module by module title using
  `[The univalence axiom](foundation.univalence.md)`, which will be displayed as
  [The univalence axiom](foundation.univalence.md).
- You can reference another module by module name using
  `` [`foundation.univalence`](foundation.univalence.md) ``, which will be
  displayed as [`foundation.univalence`](foundation.univalence.md).
- If you just want to add a clickable link, use the pattern
  `<https://unimath.github.io/agda-unimath/>`. This will be displayed as
  <https://unimath.github.io/agda-unimath/>.
- Or if you want to add a clickable link with custom text use
  `[UniMath/agda-unimath](https://github.com/UniMath/agda-unimath)`. This will
  be displayed as
  [UniMath/agda-unimath](https://github.com/UniMath/agda-unimath).

## See also

- For a template file see [`TEMPLATE.lagda.md`](TEMPLATE.lagda.md).
- An instructive example of a file with the expected structure is
  [`order-theory.galois-connections`](https://raw.githubusercontent.com/UniMath/agda-unimath/master/src/order-theory/galois-connections.lagda.md).

## Note

Please note that some of the conventions above are enforced by our `pre-commit`
hooks. You can read more about them in our
[contribution guide](CONTRIBUTING.md).

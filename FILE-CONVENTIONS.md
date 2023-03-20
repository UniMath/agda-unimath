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

Files that are part of the formalisation should be in literate Agda using
markdown. The file extension is `.lagda.md`.

### File header and module declaration

Every file should begin with a header in the following format:

```md
# The title of the file
```

and immediately after this, the module declaration and any option pragmas should
be declared.

### Imports block

After the module declaration, include an Agda code block of all module imports
starting with `<details><summary>Imports</summary>` and ending with
`</details>`. This Agda block should only contain module imports. Do not import
further modules later in the file. On the documentation pages, this Agda imports
block will be hidden by default, but it can be revealed by clicking on the
_Imports_ link.

### Sections and headings

Organize the rest of the file into sections, subsections, and possibly
subsubsections. Use `##` headings for the main sections of the file and reserve
`#` headings only for the title of the file. Common sections include `## Idea`,
`## Definitions`, and `## Properties`. Occasionally, you might include a section
like `## Examples` or `## Theorem`, based on the purpose of the file.

Ideally, the first section of a file explains the idea, the second section
proceeds to give the main definition that is the focus of the file, then the
third section proceeds possibly with examples or by deriving basic properties of
the defined concept.

### Subsections

Use `###` headings for subsections within the main sections. If a code block
following a heading is very long, you can use `####` headings to subdivide the
subsections further. Ensure that subsection headings concisely describe the
content of the following code block. However, don't hesitate to include
explanatory text within a section when necessary.

### See also and references

At the end of the file you may add a `See also` or `References` subsection where
you reference related sources such as other modules or articles related to the
contents of the file.

- You can reference another module by module title using
  `[The univalence axiom](foundation.univalence.md)`, which will be displayed as
  [The univalence axiom](foundation.univalence.md).
- You can reference another module by module name using
  ``[`foundation.univalence`](foundation.univalence.md)``, which will be
  displayed as [`foundation.univalence`](foundation.univalence.md).
- If you just want to add a clickable link, use the pattern
  `<https://unimath.github.io/agda-unimath/>`. This will be displayed as
  <https://unimath.github.io/agda-unimath/>.
- Or if you want to add a clickable link with custom text use
  `[UniMath/agda-unimath](https://github.com/UniMath/agda-unimath)`. This will
  be displayed as
  [UniMath/agda-unimath](https://github.com/UniMath/agda-unimath).

## Notes

- For a template file see [`template.lagda.md`](template.md).

- An instructive example of a file with the expected structure is
  [`foundation.cantor-schroder-bernstein-escardo`](https://raw.githubusercontent.com/UniMath/agda-unimath/master/src/foundation/cantor-schroder-bernstein-escardo.lagda.md).

Please note that some of the conventions above are enforced by our `pre-commit`
hooks. You can read more about them in our
[installation guide](HOWTO-INSTALL.md#pre-commit-hooks).

# Style conventions for files

1. File names are descriptive of the concept it introduces, or the main theorem it proves. The file names could be considered indexing terms, with the list of files functioning much like the index in the back of a book. Usually, file names consist of a noun or a noun phrase. File names should be natural, sufficiently precise, concise, and consistent with those of related files.
2. File names are entirely in lowercase, with words separated by hyphens. Words in file names should not be abbreviated unless the abbreviated term is a widely accepted mathematical term, e.g., `poset`.
3. Files that are part of the formalisation should be in literate agda using markdown. They should have the file extension `.lagda.md`.
4. Every file should begin with a header in the following format

    ```md
    # The title of the file
    ```

5. Immediately after the header, there should be an Agda block code beginning
with: `<details><summary>Imports</summary>` and ending with: `</details>`. The
Agda block should include the module declaration and all module imports. In
particular, there should be no further imports later on in the file. The module
names should always be in lowercase. By default, Agda imports will be hidden but
they can be revealed by clicking on the *Imports* link.
6. The rest of the files is divided into sections, subsections and possibly subsubsections. `##` headings are the main sections of the page. Usually at the beginning we have `## Idea` describing informally the idea of the things in that file. Then we hav `## Definitions` for definitions, and after that `## Properties` followed by `## See also` and `## References`. In rare cases we can include a section `## Examples` for examples or `## Theorem` if the main purpose of the file is to prove an important theorem. The reason `## Examples` is rarely used is that usually examples go in their own files, which can be listed under `## See also`.
`###` headings are for subsectioning the `## Definitions` and `## Properties` section. They are brief descriptions of the code block that follows. If the code block that follows is very long, we can even use `####` headings to subdivide the subsections.
Note that `#` headings are only used for the title of the page.
7. The subsections should have a markdown header of level `###` and they should concisely describe the content of the block of code that follows.
Ideally, the first section of a file explains the idea, then proceeds to give the main definition that is the focus of the current file, then proceeds possibly with examples and by deriving basic properties of the defined concept.
8. At the end of the file you may also add a `See also` or `References` subsection where you reference related sources such as other modules or articles related to the contents of the file.
    - You can reference another module by module title using
      `[the univalence axiom](foundation.univalence.md)`, which will be displayed as [the univalence axiom](foundation.univalence.md).
    - You can reference another module by module name using ```[`foundation.univalence`](foundation.univalence.md)```, which will be displayed as [`foundation.univalence`](foundation.univalence.md).
    - If you just want to add a clickable link, use the pattern `<https://unimath.github.io/agda-unimath/>`. This will be displayed as <https://unimath.github.io/agda-unimath/>.
    - Or if you want to add a clickable link with custom text use `[UniMath/agda-unimath](https://github.com/UniMath/agda-unimath)`.
      This will be displayed as [UniMath/agda-unimath](https://github.com/UniMath/agda-unimath).

A good reference file for the expected structure of a file is [`foundation.cantor-schroder-bernstein-escardo`](https://raw.githubusercontent.com/UniMath/agda-unimath/master/src/foundation/cantor-schroder-bernstein-escardo.lagda.md).

Please note that some conventions above are checks enforced by our pre-commit hooks, read more about them in [HOWTO-INSTALL.md](HOWTO-INSTALL.md#pre-commit-hooks).

# Visualization of definitions in the library

Below you may find an interactive explorer of modules and definitions in
agda-unimath, including search and checking if one definition depends on
another. Hover over the information icon for detailed usage instructions.

<div id="small-display-notice" style="display:none">
  ⚠ The explorer is not optimized for small screens. It may be
  difficult to control on mobile devices.
</div>

<style>
  .sidetoc { display: none; }
  @media(max-width:1100px) {
    #small-display-notice { display: block; }
  }
</style>

<div align="center">
  <iframe
    src="https://jobpetrovcic.github.io/Unimath-Visualization-Deployment/visualize"
    style="background: white"
    scrolling="no"
    width="1000"
    height="600"
    referrerpolicy="no-referrer">
  </iframe>
</div>

The interactive explorer was developed by Job Petrovčič. Vojtěch Štěpančík,
Matej Petković, and Andrej Bauer contributed invaluable suggestions and offered
helpful support. It's built and deployed outside of the agda-unimath repository,
using a fork of Agda. For that reason the definitions in the graph may lag
behind the definitions on the website by a few hours.

The explorer has a few known limitations. Most noticeably it doesn't recognize
the `open import ... renaming (X to Y) public` pattern of exporting definitions,
so in particular the
[`foundation.universe-levels`](foundation.universe-levels.md) module is not
shown, and references to `UU` in the source code show up as references to
`Agda.Primitive.Set`. Note that one of the consequences is that two `Prop`s
appear in the search results --- the first one being `Agda.Primitive.Prop`,
which is Agda's
[proof-irrelevant sort](https://agda.readthedocs.io/en/latest/language/prop.html)
and isn't used anywhere in the library, and the second being agda-unimath's
[`foundation-core.propositions.Prop`](foundation-core.propositions.md), which is
the type of homotopy propositions.

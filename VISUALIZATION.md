# Interactive explorer of the library

Below is an interactive explorer of modules and definitions in agda-unimath. It
displays various properties of the nodes in the dependency graph, and also
allows you to determine dependencies between individual definitions. Hover over
ⓘ for detailed usage instructions.

<p id="small-display-notice" style="display:none">
  ⚠ The explorer is not optimized for small screens. It may be
  difficult to control on mobile devices.
</p>

<style>
  .sidetoc { display: none; }
  @media(max-width:1100px) {
    #small-display-notice { display: block !important; }
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

The interactive explorer was developed by
[Job Petrovčič](https://github.com/JobPetrovcic). In addition,
[Vojtěch Štěpančík](https://vojtechstep.eu/), Matej Petković, and
[Andrej Bauer](https://www.andrej.com) contributed invaluable suggestions and
offered helpful support.

### Notes

The explorer is built and deployed outside of the agda-unimath repository, using
a fork of Agda. For that reason the definitions in the graph may lag behind the
definitions on the website by a few hours.

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

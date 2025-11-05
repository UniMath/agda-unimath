# Stereoisomerism for enriched undirected graphs

```agda
module graph-theory.stereoisomerism-enriched-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels

open import graph-theory.enriched-undirected-graphs
open import graph-theory.equivalences-undirected-graphs
```

</details>

## Idea

A
{{#concept "stereoisomerism" Disambiguation="between enriched undirected graphs" WD="stereoisomerism" WDID=Q47455153  Agda=stereoisomerism-Enriched-Undirected-Graph}}
between two
`(A,B)`-[enriched undirected graphs](graph-theory.enriched-undirected-graphs.md)
is an [equivalence](graph-theory.equivalences-undirected-graphs.md) between
their underlying [undirected graphs](graph-theory.undirected-graphs.md)
preserving the shape of the vertices. This concept is derived from the concept
of stereoisomerism of chemical compounds.

**Note:** It could be that we only want the shapes to be merely preserved.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (G : Enriched-Undirected-Graph l3 l4 A B)
  (H : Enriched-Undirected-Graph l5 l6 A B)
  where

  stereoisomerism-Enriched-Undirected-Graph :
    UU (lsuc lzero ⊔ l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  stereoisomerism-Enriched-Undirected-Graph =
    Σ ( equiv-Undirected-Graph
        ( undirected-graph-Enriched-Undirected-Graph A B G)
        ( undirected-graph-Enriched-Undirected-Graph A B H))
      ( λ e →
        ( shape-vertex-Enriched-Undirected-Graph A B G) ~
        ( ( shape-vertex-Enriched-Undirected-Graph A B H) ∘
          ( vertex-equiv-Undirected-Graph
            ( undirected-graph-Enriched-Undirected-Graph A B G)
            ( undirected-graph-Enriched-Undirected-Graph A B H)
            ( e))))
```

## External links

- [Stereoisomerism](https://www.wikidata.org/entity/Q47455153) on Wikidata
- [Stereoisomerism](https://en.wikipedia.org/wiki/Stereoisomerism) at Wikipedia

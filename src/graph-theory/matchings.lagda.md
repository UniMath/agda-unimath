# Matchings

```agda
module graph-theory.matchings where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "matching" WD="matching" WDID=Q1065144 Disambiguation="in a undirected graph" Agda=matching}}
in an [undirected graph](graph-theory.undirected-graphs.md) is a type of edges
without common vertices.

## Definitions

```agda
module _
  {l1 l2 : Level}
  where

  selected-edges-vertex-Undirected-Graph :
    ( G : Undirected-Graph l1 l2) →
    ( (p : unordered-pair-vertices-Undirected-Graph G) →
      edge-Undirected-Graph G p → Fin 2) →
    vertex-Undirected-Graph G → UU (l1 ⊔ l2)
  selected-edges-vertex-Undirected-Graph G c x =
    Σ ( vertex-Undirected-Graph G)
      ( λ y →
        Σ ( edge-Undirected-Graph G (standard-unordered-pair x y))
          ( λ e → c (standard-unordered-pair x y) e ＝ inr star))

  matching : Undirected-Graph l1 l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
  matching G =
    Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p → Fin 2)
      ( λ c →
        ( x : vertex-Undirected-Graph G) →
        is-prop (selected-edges-vertex-Undirected-Graph G c x))

  perfect-matching : Undirected-Graph l1 l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
  perfect-matching G =
    Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p → Fin 2)
      ( λ c →
        ( x : vertex-Undirected-Graph G) →
          is-contr (selected-edges-vertex-Undirected-Graph G c x))
```

## External links

- [Matching](https://www.wikidata.org/entity/Q1065144) on Wikidata
- [Matching (graph theory)](<https://en.wikipedia.org/wiki/Matching_(graph_theory)>)
  at Wikipedia
- [Matching](https://mathworld.wolfram.com/Matching.html) at Wolfram MathWorld

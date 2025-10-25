# Complete bipartite graphs

```agda
module graph-theory.complete-bipartite-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-graphs

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Consider two [finite sets](univalent-combinatorics.finite-types.md) `X` and `Y`.
The
{{#concept "complete bipartite graph" Agda=complete-bipartite-Finite-Undirected-Graph WDID=Q913598 WD="complete bipartite graph"}}
on `X` and `Y` is the [undirected finite graph](graph-theory.finite-graphs.md)
consisting of:

- The finite set of vertices is the
  [coproduct type](univalent-combinatorics.coproduct-types.md) `X + Y`.
- Given an [unordered pair](foundation.unordered-pairs.md) `f : I → X + Y` of
  vertices, the finite type of edges on the unordered pair `(I , f)` is given by

  ```text
    (Σ (x : X), fiber f (inl x))  × (Σ (y : Y), fiber f (inr y)).
  ```

  In other words, an unordered pair of elements of the coproduct type `X + Y` is
  an edge in the complete bipartite graph on `X` and `Y` precisely when one of
  the elements of the unordered pair comes from `X` and the other comes from
  `Y`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Finite-Type l1) (Y : Finite-Type l2)
  where

  vertex-finite-type-complete-bipartite-Finite-Undirected-Graph :
    Finite-Type (l1 ⊔ l2)
  vertex-finite-type-complete-bipartite-Finite-Undirected-Graph =
    coproduct-Finite-Type X Y

  vertex-complete-bipartite-Finite-Undirected-Graph : UU (l1 ⊔ l2)
  vertex-complete-bipartite-Finite-Undirected-Graph =
    type-Finite-Type
      vertex-finite-type-complete-bipartite-Finite-Undirected-Graph

  unordered-pair-vertices-complete-bipartite-Finite-Undirected-Graph :
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  unordered-pair-vertices-complete-bipartite-Finite-Undirected-Graph =
    unordered-pair vertex-complete-bipartite-Finite-Undirected-Graph

  edge-finite-type-complete-bipartite-Finite-Undirected-Graph :
    unordered-pair-vertices-complete-bipartite-Finite-Undirected-Graph →
    Finite-Type (l1 ⊔ l2)
  edge-finite-type-complete-bipartite-Finite-Undirected-Graph p =
    product-Finite-Type
      ( Σ-Finite-Type X
        ( λ x →
          fiber-Finite-Type
            ( finite-type-2-Element-Type (pr1 p))
            ( coproduct-Finite-Type X Y)
            ( element-unordered-pair p)
            ( inl x)))
      ( Σ-Finite-Type Y
        ( λ y →
          fiber-Finite-Type
            ( finite-type-2-Element-Type (pr1 p))
            ( coproduct-Finite-Type X Y)
            ( element-unordered-pair p)
            ( inr y)))

  edge-complete-bipartite-Undirected-Graph :
    unordered-pair-vertices-complete-bipartite-Finite-Undirected-Graph →
    UU (l1 ⊔ l2)
  edge-complete-bipartite-Undirected-Graph p =
    type-Finite-Type
      ( edge-finite-type-complete-bipartite-Finite-Undirected-Graph p)

  complete-bipartite-Finite-Undirected-Graph :
    Finite-Undirected-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 complete-bipartite-Finite-Undirected-Graph =
    vertex-finite-type-complete-bipartite-Finite-Undirected-Graph
  pr2 complete-bipartite-Finite-Undirected-Graph =
    edge-finite-type-complete-bipartite-Finite-Undirected-Graph
```

## External links

- [Complete bipartite graph](https://d3gt.com/unit.html?complete-bipartite) at
  D3 Graph Theory
- [Bipartite graphs](https://ncatlab.org/nlab/show/bipartite+graph) at $n$Lab
- [Complete bipartite graph](https://www.wikidata.org/entity/Q913598) at
  Wikidata
- [Complete bipartite graph](https://en.wikipedia.org/wiki/Complete_bipartite_graph)
  at Wikipedia
- [Complete bipartite graphs](https://mathworld.wolfram.com/CompleteBipartiteGraph.html)
  at Wolfram MathWorld

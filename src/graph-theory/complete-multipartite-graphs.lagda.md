# Complete multipartite graphs

```agda
module graph-theory.complete-multipartite-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-graphs

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
```

</details>

## Idea

Consider a family of [finite types](univalent-combinatorics.finite-types.md) `Y`
indexed by a finite type `X`. The
{{#concept "complete multipartite graph" Agda=complete-multipartite-Finite-Undirected-Graph WD="multipartite graph" WDID=Q1718082}}
at `Y` is the [finite undirected graph](graph-theory.finite-graphs.md)
consisting of:

- The finite type of vertices is the
  [dependent pair type](univalent-combinatorics.dependent-pair-types.md)
  `Σ (x : X), Y x`.
- An [unordered pair](foundation.unordered-pairs.md) `f : I → Σ (x : X), Y x` is
  an edge if the induced unordered pair `pr1 ∘ f : I → X` is an
  [embedding](foundation-core.embeddings.md).

**Note:** The formalization of the finite type of edges below is different from
the above description, and needs to be changed.

## Definitions

### Complete multipartite graphs

```agda
module _
  {l1 l2 : Level} (X : Finite-Type l1) (Y : type-Finite-Type X → Finite-Type l2)
  where

  vertex-finite-type-complete-multipartite-Finite-Undirected-Graph :
    Finite-Type (l1 ⊔ l2)
  vertex-finite-type-complete-multipartite-Finite-Undirected-Graph =
    Σ-Finite-Type X Y

  vertex-complete-multipartite-Finite-Undirected-Graph : UU (l1 ⊔ l2)
  vertex-complete-multipartite-Finite-Undirected-Graph =
    type-Finite-Type
      vertex-finite-type-complete-multipartite-Finite-Undirected-Graph

  unordered-pair-vertices-complete-multipartite-Finite-Undirected-Graph :
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  unordered-pair-vertices-complete-multipartite-Finite-Undirected-Graph =
    unordered-pair vertex-complete-multipartite-Finite-Undirected-Graph

  edge-finite-type-complete-multipartite-Finite-Undirected-Graph :
    unordered-pair-vertices-complete-multipartite-Finite-Undirected-Graph →
    Finite-Type l1
  edge-finite-type-complete-multipartite-Finite-Undirected-Graph p =
    ( Π-Finite-Type
      ( finite-type-2-Element-Type (pr1 p))
      ( λ x →
        Π-Finite-Type
          ( finite-type-2-Element-Type (pr1 p))
          ( λ y →
            Id-Finite-Type X
              ( pr1 (element-unordered-pair p x))
              ( pr1 (element-unordered-pair p y))))) →𝔽
    ( empty-Finite-Type)

  edge-complete-multipartite-Finite-Undirected-Graph :
    unordered-pair-vertices-complete-multipartite-Finite-Undirected-Graph →
    UU l1
  edge-complete-multipartite-Finite-Undirected-Graph p =
    type-Finite-Type
      ( edge-finite-type-complete-multipartite-Finite-Undirected-Graph p)

  complete-multipartite-Finite-Undirected-Graph :
    Finite-Undirected-Graph (l1 ⊔ l2) l1
  pr1 complete-multipartite-Finite-Undirected-Graph =
    vertex-finite-type-complete-multipartite-Finite-Undirected-Graph
  pr2 complete-multipartite-Finite-Undirected-Graph =
    edge-finite-type-complete-multipartite-Finite-Undirected-Graph
```

## External links

- [Multipartite graph](https://www.wikidata.org/entity/Q1718082) on Wikidata
- [Multipartite graph](https://en.wikipedia.org/wiki/Multipartite_graph) on
  Wikipedia
- [Complete multipartite graph](https://mathworld.wolfram.com/CompleteMultipartiteGraph.html)
  on Wolfram MathWorld

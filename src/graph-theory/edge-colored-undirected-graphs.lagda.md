# Edge-colored undirected graphs

```agda
module graph-theory.edge-colored-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.neighbors-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

An
{{#concept "edge-colored undirected graph" Agda=Edge-Colored-Undirected-Graph}}
is an [undirected graph](graph-theory.undirected-graphs.md) equipped with a
family of maps `E p → X` from the edges at
[unordered pairs](foundation.unordered-pairs.md) `p` into a type `C` of colors,
such that the induced map `incident-Undirected-Graph G x → C` is
[injective](foundation.injective-maps.md) for each vertex `x`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (C : UU l1) (G : Undirected-Graph l2 l3)
  where

  neighbor-edge-coloring-Undirected-Graph :
    ( (p : unordered-pair-vertices-Undirected-Graph G) →
      edge-Undirected-Graph G p → C) →
    (x : vertex-Undirected-Graph G) → neighbor-Undirected-Graph G x → C
  neighbor-edge-coloring-Undirected-Graph f x (pair y e) =
    f (standard-unordered-pair x y) e

  edge-coloring-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3)
  edge-coloring-Undirected-Graph =
    Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p → C)
      ( λ f →
        (x : vertex-Undirected-Graph G) →
        is-emb (neighbor-edge-coloring-Undirected-Graph f x))

Edge-Colored-Undirected-Graph :
  {l : Level} (l1 l2 : Level) (C : UU l) → UU (l ⊔ lsuc l1 ⊔ lsuc l2)
Edge-Colored-Undirected-Graph l1 l2 C =
  Σ ( Undirected-Graph l1 l2)
    ( edge-coloring-Undirected-Graph C)

module _
  {l1 l2 l3 : Level} {C : UU l1} (G : Edge-Colored-Undirected-Graph l2 l3 C)
  where

  undirected-graph-Edge-Colored-Undirected-Graph : Undirected-Graph l2 l3
  undirected-graph-Edge-Colored-Undirected-Graph = pr1 G

  vertex-Edge-Colored-Undirected-Graph : UU l2
  vertex-Edge-Colored-Undirected-Graph =
    vertex-Undirected-Graph undirected-graph-Edge-Colored-Undirected-Graph

  unordered-pair-vertices-Edge-Colored-Undirected-Graph : UU (lsuc lzero ⊔ l2)
  unordered-pair-vertices-Edge-Colored-Undirected-Graph =
    unordered-pair-vertices-Undirected-Graph
      undirected-graph-Edge-Colored-Undirected-Graph

  edge-Edge-Colored-Undirected-Graph :
    unordered-pair-vertices-Edge-Colored-Undirected-Graph → UU l3
  edge-Edge-Colored-Undirected-Graph =
    edge-Undirected-Graph undirected-graph-Edge-Colored-Undirected-Graph

  neighbor-Edge-Colored-Undirected-Graph :
    vertex-Edge-Colored-Undirected-Graph → UU (l2 ⊔ l3)
  neighbor-Edge-Colored-Undirected-Graph =
    neighbor-Undirected-Graph undirected-graph-Edge-Colored-Undirected-Graph

  coloring-Edge-Colored-Undirected-Graph :
    (p : unordered-pair-vertices-Edge-Colored-Undirected-Graph) →
    edge-Edge-Colored-Undirected-Graph p → C
  coloring-Edge-Colored-Undirected-Graph =
    pr1 (pr2 G)

  neighbor-coloring-Edge-Colored-Undirected-Graph :
    (x : vertex-Edge-Colored-Undirected-Graph) →
    neighbor-Edge-Colored-Undirected-Graph x → C
  neighbor-coloring-Edge-Colored-Undirected-Graph =
    neighbor-edge-coloring-Undirected-Graph C
      undirected-graph-Edge-Colored-Undirected-Graph
      coloring-Edge-Colored-Undirected-Graph

  is-emb-coloring-Edge-Colored-Undirected-Graph :
    (x : vertex-Edge-Colored-Undirected-Graph) →
    is-emb (neighbor-coloring-Edge-Colored-Undirected-Graph x)
  is-emb-coloring-Edge-Colored-Undirected-Graph =
    pr2 (pr2 G)
```

## External links

- [Edge coloring](https://en.wikipedia.org/wiki/Edge_coloring) at Wikipedia
- [Edge coloring](https://mathworld.wolfram.com/EdgeColoring.html) at Wolfram
  MathWorld
- [Graph coloring](https://www.wikidata.org/entity/Q504843) on Wikidata

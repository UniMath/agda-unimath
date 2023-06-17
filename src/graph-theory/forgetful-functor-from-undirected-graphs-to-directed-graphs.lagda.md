# The forgetful functor from undirected graphs to directed graphs

```agda
module
  graph-theory.forgetful-functor-from-undirected-graphs-to-directed-graphs
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.directed-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

The **forgetful functor** from
[undirected graphs](graph-theory.undirected-graphs.md) to
[directed graphs](graph-theory.directed-graphs.md) takes an undirected graph `G`
and returns the directed graphs in which we have an edge from both `x` to `y`
and from `y` to `x` for every undirected edge on the
[standard unordered pair](foundation.unordered-pairs.md) `{x,y}`.

## Definitions

### The forgetful functor from undirected graphs to directed graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  vertex-graph-Undirected-Graph : UU l1
  vertex-graph-Undirected-Graph = vertex-Undirected-Graph G

  edge-graph-Undirected-Graph :
    (x y : vertex-graph-Undirected-Graph) → UU l2
  edge-graph-Undirected-Graph x y =
    edge-Undirected-Graph G (standard-unordered-pair x y)

  graph-Undirected-Graph : Directed-Graph l1 l2
  pr1 graph-Undirected-Graph = vertex-graph-Undirected-Graph
  pr2 graph-Undirected-Graph = edge-graph-Undirected-Graph

  directed-edge-edge-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph G)
    (e : edge-Undirected-Graph G p)
    (i : type-unordered-pair p) →
    edge-graph-Undirected-Graph
      ( element-unordered-pair p i)
      ( other-element-unordered-pair p i)
  directed-edge-edge-Undirected-Graph p e i =
    tr-edge-Undirected-Graph G
      ( p)
      ( standard-unordered-pair
        ( element-unordered-pair p i)
        ( other-element-unordered-pair p i))
      ( inv-Eq-unordered-pair
        ( standard-unordered-pair
          ( element-unordered-pair p i)
          ( other-element-unordered-pair p i))
        ( p)
        ( compute-standard-unordered-pair-element-unordered-pair p i))
      ( e)
```

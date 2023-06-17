# The forgetful functor from directed graphs to undirected graphs

```agda
module
  graph-theory.forgetful-functor-from-directed-graphs-to-undirected-graphs
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.symmetric-binary-relations
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

The **forgetful functor** from
[directed graphs](graph-theory.directed-graphs.md) to
[undirected graphs](graph-theory.undirected-graphs.md) forgets the direction of
directed edges.

## Definitions

### The operation on directed graphs that forgets the directions of the edges

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  vertex-undirected-graph-Directed-Graph : UU l1
  vertex-undirected-graph-Directed-Graph = vertex-Directed-Graph G

  edge-undirected-graph-Directed-Graph :
    symmetric-binary-relation l2 vertex-undirected-graph-Directed-Graph
  edge-undirected-graph-Directed-Graph =
    symmetric-binary-relation-Rel (edge-Directed-Graph G)

  undirected-graph-Graph : Undirected-Graph l1 l2
  pr1 undirected-graph-Graph = vertex-undirected-graph-Directed-Graph
  pr2 undirected-graph-Graph = edge-undirected-graph-Directed-Graph
```

# The undirected core of a directed graph

```agda
module graph-theory.undirected-core-directed-graphs where
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

The **undirected core** of a [directed graph](graph-theory.directed-graphs.md)
`G` is the universal [undirected graph](graph-theory.undirected-graphs.md)
`undirected-core G` equipped with a
[morphism of directed graphs](graph-theory.morphisms-directed-graphs.md)

```text
  undirected-core G → G.
```

## Definitions

### The undirected core of a directed graph

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  vertex-undirected-core-Directed-Graph : UU l1
  vertex-undirected-core-Directed-Graph = vertex-Directed-Graph G

  edge-undirected-core-Directed-Graph :
    symmetric-binary-relation l2 vertex-undirected-core-Directed-Graph
  edge-undirected-core-Directed-Graph =
    symmetric-core-Rel (edge-Directed-Graph G)

  undirected-core-Directed-Graph : Undirected-Graph l1 l2
  pr1 undirected-core-Directed-Graph = vertex-undirected-core-Directed-Graph
  pr2 undirected-core-Directed-Graph = edge-undirected-core-Directed-Graph
```

# Acyclic undirected graphs

```agda
module graph-theory.acyclic-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import graph-theory.geometric-realizations-undirected-graphs
open import graph-theory.reflecting-maps-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

An {{#concept "acyclic undirected graph" WDID=Q3115453 WD="Acyclic graph"}} is
an [undirected graph](graph-theory.undirected-graphs.md) of which the
[geometric realization](graph-theory.geometric-realizations-undirected-graphs.md)
is [contractible](foundation-core.contractible-types.md).

The notion of acyclic graphs is a generalization of the notion of
[undirected trees](trees.undirected-trees.md). Note that in this library, an
undirected tree is an undirected graph in which the type of
[trails](graph-theory.trails-undirected-graphs.md) between any two points is
contractible. The type of nodes of such undirected trees consequently has
[decidable equality](foundation.decidable-equality.md). On the other hand, there
are acyclic undirected graphs that are not undirected trees in this sense. One
way to obtain them is via
[acyclic types](synthetic-homotopy-theory.acyclic-types.md), which are types of
which the [suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
contractible. The undirected suspension diagram of such types is an acyclic
graph. Furthermore, any [directed tree](trees.directed-trees.md) induces an
acyclic undirected graph by forgetting the directions of the edges.

## Definition

### Acyclic undirected graphs

The following is a preliminary definition that requires us to parametrize over
an extra universe level. This will not be necessary anymore if we constructed a
geometric realization of every undirected graph. Once we did that, we would
simply say that the geometric realization of `G` is contractible.

```agda
is-acyclic-Undirected-Graph :
  {l1 l2 : Level} (l : Level) (G : Undirected-Graph l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
is-acyclic-Undirected-Graph l G =
  is-geometric-realization-reflecting-map-Undirected-Graph l G
    ( terminal-reflecting-map-Undirected-Graph G)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}

## External links

- [Trees](https://ncatlab.org/nlab/show/tree) at $n$Lab
- [Forests](<https://en.wikipedia.org/wiki/Tree_(graph_theory)#Forest>) at
  Wikipedia
- [Acyclic graphs](https://mathworld.wolfram.com/AcyclicGraph.html) at Wolfram
  Mathworld.

# Complete undirected graphs

```agda
module graph-theory.complete-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import graph-theory.complete-multipartite-graphs
open import graph-theory.finite-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A
{{#concept "complete undirected graph" Agda=complete-Finite-Undirected-Graph WD="complete graph" WDID=Q45715}}
is a [complete multipartite graph](graph-theory.complete-multipartite-graphs.md)
in which every block has exactly one vertex. In other words, it is an
[undirected graph](graph-theory.undirected-graphs.md) in which every vertex is
connected to every other vertex.

There are many ways of presenting complete undirected graphs. For example, the
type of edges in a complete undirected graph is a
[2-element subtype](univalent-combinatorics.2-element-subtypes.md) of the type
of its vertices.

## Definition

```agda
complete-Finite-Undirected-Graph :
  {l : Level} → Finite-Type l → Finite-Undirected-Graph l l
complete-Finite-Undirected-Graph X =
  complete-multipartite-Finite-Undirected-Graph X (λ x → unit-Finite-Type)
```

## External links

- [Complete graph](https://d3gt.com/unit.html?complete-graph) at D3 Graph theory
- [Complete graph](https://www.wikidata.org/entity/Q45715) on Wikidata
- [Complete graph](https://en.wikipedia.org/wiki/Complete_graph) on Wikipedia
- [Complete graph](https://mathworld.wolfram.com/CompleteGraph.html) at Wolfram
  MathWorld

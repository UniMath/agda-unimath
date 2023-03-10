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

A complete undirected graph is a complete multipartite graph in which every block has exactly one vertex. In other words, it is an undirected graph in which every vertex is connected to every other vertex.

There are many ways of presenting complete undirected graphs. For example, the type of edges in a complete undirected graph is a 2-element subtype of the type of its vertices.

## Definition

```agda
complete-Undirected-Graph-𝔽 : {l : Level} → 𝔽 l → Undirected-Graph-𝔽 l l
complete-Undirected-Graph-𝔽 X = complete-multipartite-Undirected-Graph-𝔽 X (λ x → unit-𝔽)
```

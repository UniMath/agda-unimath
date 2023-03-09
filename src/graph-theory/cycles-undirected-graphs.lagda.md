# Cycles in undirected graphs

```agda
module graph-theory.cycles-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.embeddings-undirected-graphs
open import graph-theory.polygons
open import graph-theory.undirected-graphs
```

</details>

## Idea

A cycle in an undirected graph `G` consists of a `k`-gon `H` equipped with an embedding of graphs from `H` into `G`.

## Definition

```agda
module _
  {l1 l2 : Level} (k : ℕ) (G : Undirected-Graph l1 l2)
  where

  cycle-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  cycle-Undirected-Graph =
    Σ (Polygon k) (λ H → emb-Undirected-Graph (undirected-graph-Polygon k H) G)
```

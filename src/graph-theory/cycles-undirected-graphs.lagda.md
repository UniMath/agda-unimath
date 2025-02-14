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

A
{{#concept "cycle" Agda=cycle-Undirected-Graph Disambiguation="undirected graph" WD="cycle" WDID=Q245595}}
in an [undirected graph](graph-theory.undirected-graphs.md) `G` consists of a
[`k`-gon](graph-theory.polygons.md) `H` equipped with an
[embedding of graphs](graph-theory.embeddings-undirected-graphs.md) from `H`
into `G`.

## Definition

```agda
module _
  {l1 l2 : Level} (k : ℕ) (G : Undirected-Graph l1 l2)
  where

  cycle-Undirected-Graph : UU (lone ⊔ l1 ⊔ l2)
  cycle-Undirected-Graph =
    Σ (Polygon k) (λ H → emb-Undirected-Graph (undirected-graph-Polygon k H) G)
```

## External links

- [Cycle](https://www.wikidata.org/entity/Q245595) on Wikidata
- [Cycle (graph theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>)
  at Wikipedia
- [Graph cycle](https://mathworld.wolfram.com/GraphCycle.html) at Wolfram
  MathWorld

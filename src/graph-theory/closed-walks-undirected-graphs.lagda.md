# Closed walks in undirected graphs

```agda
module graph-theory.closed-walks-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.morphisms-undirected-graphs
open import graph-theory.polygons
open import graph-theory.undirected-graphs
```

</details>

## Idea

A
{{#concept "closed walk" Agda=closed-walk-Undirected-Graph Disambiguation="undirected graph" WDID=Q245595 WD="cycle"}}
of length `k : ℕ` in an [undirected graph](graph-theory.undirected-graphs.md)
`G` is a [morphism](graph-theory.morphisms-undirected-graphs.md) of graphs from
a [`k`-gon](graph-theory.polygons.md) into `G`.

## Definition

```agda
module _
  {l1 l2 : Level} (k : ℕ) (G : Undirected-Graph l1 l2)
  where

  closed-walk-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  closed-walk-Undirected-Graph =
    Σ (Polygon k) (λ H → hom-Undirected-Graph (undirected-graph-Polygon k H) G)
```

## External links

- [Cycle](https://www.wikidata.org/entity/Q245595) at Wikidata
- [Cycle (Graph Theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>)
  at Wikipedia
- [Graph Cycle](https://mathworld.wolfram.com/GraphCycle.html) at Wolfram
  MathWorld

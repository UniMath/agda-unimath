# Circuits in undirected graphs

```agda
module graph-theory.circuits-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.polygons
open import graph-theory.totally-faithful-morphisms-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

A
{{#concept "circuit" Disambiguation="in an undirected graph" Agda=circuit-Undirected-Graph WD="cycle" WDID=Q245595}}
in an [undirected graph](graph-theory.undirected-graphs.md) `G` consists of a
[`k`-gon](graph-theory.polygons.md) `H` equipped with a
[totally faithful](graph-theory.totally-faithful-morphisms-undirected-graphs.md)
[morphism](graph-theory.morphisms-undirected-graphs.md) of undirected graphs
from `H` to `G`. In other words, a circuit is a closed walk with no repeated
edges.

## Definition

```agda
module _
  {l1 l2 : Level} (k : ℕ) (G : Undirected-Graph l1 l2)
  where

  circuit-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  circuit-Undirected-Graph =
    Σ ( Polygon k)
      ( λ H →
        totally-faithful-hom-Undirected-Graph (undirected-graph-Polygon k H) G)
```

## External links

- [Cycle (Graph Theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>)
  at Wikipedia
- [Graph Cycle](https://mathworld.wolfram.com/GraphCycle.html) at Wolfram
  MathWorld

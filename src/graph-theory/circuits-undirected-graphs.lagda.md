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

A circuit in an undirected graph `G` consists of a `k`-gon `H` equipped with a totally faithful morphism of graphs from `H` to `G`. In other words, a circuit is a closed walk with no repeated edges.

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

# Polygons

```agda
module graph-theory.polygons where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.functoriality-propositional-truncation
open import foundation.mere-equivalences
open import foundation.sets
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.equivalences-undirected-graphs
open import graph-theory.mere-equivalences-undirected-graphs
open import graph-theory.undirected-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A {{#concept "polygon" WD="polygon" WDID=Q37555 Agda=Polygon}} is an
[undirected graph](graph-theory.undirected-graphs.md) that is
[merely equivalent](graph-theory.mere-equivalences-undirected-graphs.md) to a
graph with vertices the underlying type of the
[standard cyclic group](elementary-number-theory.standard-cyclic-groups.md)
`ℤ-Mod k` and an edge from each `x ∈ ℤ-Mod k` to `x+1`. This defines for each
`k ∈ ℕ` the type of all `k`-gons. The type of all `k`-gons is a concrete
presentation of the [dihedral group](group-theory.dihedral-groups.md) `Dₖ`.

## Definition

### Standard polygons

```agda
vertex-standard-polygon-Undirected-Graph : ℕ → UU lzero
vertex-standard-polygon-Undirected-Graph k = ℤ-Mod k

unordered-pair-vertices-standard-polygon-Undirected-Graph : ℕ → UU (lsuc lzero)
unordered-pair-vertices-standard-polygon-Undirected-Graph k =
  unordered-pair (vertex-standard-polygon-Undirected-Graph k)

edge-standard-polygon-Undirected-Graph :
  (k : ℕ) →
  unordered-pair-vertices-standard-polygon-Undirected-Graph k → UU lzero
edge-standard-polygon-Undirected-Graph k p =
  Σ ( type-unordered-pair p)
    ( λ x →
      fiber
        ( element-unordered-pair p)
        ( succ-ℤ-Mod k (element-unordered-pair p x)))

standard-polygon-Undirected-Graph : ℕ → Undirected-Graph lzero lzero
pr1 (standard-polygon-Undirected-Graph k) =
  vertex-standard-polygon-Undirected-Graph k
pr2 (standard-polygon-Undirected-Graph k) =
  edge-standard-polygon-Undirected-Graph k
```

### The type of all polygons with `k` vertices

```agda
Polygon : ℕ → UU (lsuc lzero)
Polygon k =
  Σ ( Undirected-Graph lzero lzero)
    ( mere-equiv-Undirected-Graph (standard-polygon-Undirected-Graph k))

module _
  (k : ℕ) (X : Polygon k)
  where

  undirected-graph-Polygon : Undirected-Graph lzero lzero
  undirected-graph-Polygon = pr1 X

  mere-equiv-Polygon :
    mere-equiv-Undirected-Graph
      ( standard-polygon-Undirected-Graph k)
      ( undirected-graph-Polygon)
  mere-equiv-Polygon = pr2 X

  vertex-Polygon : UU lzero
  vertex-Polygon = vertex-Undirected-Graph undirected-graph-Polygon

  unordered-pair-vertices-Polygon : UU (lsuc lzero)
  unordered-pair-vertices-Polygon = unordered-pair vertex-Polygon

  edge-Polygon : unordered-pair-vertices-Polygon → UU lzero
  edge-Polygon = edge-Undirected-Graph undirected-graph-Polygon

  vertex-mere-equiv-Polygon : mere-equiv (ℤ-Mod k) vertex-Polygon
  vertex-mere-equiv-Polygon =
    map-trunc-Prop
      ( vertex-equiv-equiv-Undirected-Graph
        ( standard-polygon-Undirected-Graph k)
        ( undirected-graph-Polygon))
      ( mere-equiv-Polygon)

  is-finite-vertex-Polygon : is-nonzero-ℕ k → is-finite vertex-Polygon
  is-finite-vertex-Polygon H =
    is-finite-mere-equiv vertex-mere-equiv-Polygon (is-finite-ℤ-Mod H)

  is-set-vertex-Polygon : is-set vertex-Polygon
  is-set-vertex-Polygon =
    is-set-mere-equiv' vertex-mere-equiv-Polygon (is-set-ℤ-Mod k)

  has-decidable-equality-vertex-Polygon : has-decidable-equality vertex-Polygon
  has-decidable-equality-vertex-Polygon =
    has-decidable-equality-mere-equiv'
      ( vertex-mere-equiv-Polygon)
      ( has-decidable-equality-ℤ-Mod k)
```

## Properties

### The type of vertices of a polygon is a set

```agda
is-set-vertex-standard-polygon-Undirected-Graph :
  (k : ℕ) → is-set (vertex-standard-polygon-Undirected-Graph k)
is-set-vertex-standard-polygon-Undirected-Graph k = is-set-ℤ-Mod k
```

### Every edge is between distinct points

This remains to be formalized.

### Every polygon is a simple graph

This remains to be formalized.

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}

## External links

- [Cycle graph](https://www.wikidata.org/entity/Q622506) on Wikidata
- [Cycle graph](https://en.wikipedia.org/wiki/Cycle_graph) at Wikipedia
- [Cycle graph](https://mathworld.wolfram.com/CycleGraph.html) at Wolfram
  MathWorld

# Fibers of directed trees

```agda
module trees.fibers-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.fibers-directed-graphs

open import trees.bases-directed-trees
open import trees.directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

The
{{#concept "fiber" Disambiguation="of a directed tree" Agda=fiber-Directed-Tree}}
of a [directed tree](trees.directed-trees.md) `T` at a node `x` consists of all
nodes `y` equipped with a [walk](graph-theory.walks-directed-graphs.md)
`w : walk T y x`. An edge from `(y, w)` to `(z , v)` consists of an edge
`e : edge T x y` such that `w ＝ cons-walk e v`.

## Definitions

### The underlying graph of the fiber of `T` at `x`

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2) (x : node-Directed-Tree T)
  where

  node-fiber-Directed-Tree : UU (l1 ⊔ l2)
  node-fiber-Directed-Tree =
    node-fiber-Directed-Graph (graph-Directed-Tree T) x

  node-inclusion-fiber-Directed-Tree :
    node-fiber-Directed-Tree → node-Directed-Tree T
  node-inclusion-fiber-Directed-Tree =
    node-inclusion-fiber-Directed-Graph (graph-Directed-Tree T) x

  walk-node-inclusion-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree) →
    walk-Directed-Tree T (node-inclusion-fiber-Directed-Tree y) x
  walk-node-inclusion-fiber-Directed-Tree =
    walk-node-inclusion-fiber-Directed-Graph (graph-Directed-Tree T) x

  root-fiber-Directed-Tree : node-fiber-Directed-Tree
  root-fiber-Directed-Tree =
    root-fiber-Directed-Graph (graph-Directed-Tree T) x

  is-root-fiber-Directed-Tree : node-fiber-Directed-Tree → UU (l1 ⊔ l2)
  is-root-fiber-Directed-Tree =
    is-root-fiber-Directed-Graph (graph-Directed-Tree T) x

  edge-fiber-Directed-Tree : (y z : node-fiber-Directed-Tree) → UU (l1 ⊔ l2)
  edge-fiber-Directed-Tree =
    edge-fiber-Directed-Graph (graph-Directed-Tree T) x

  edge-inclusion-fiber-Directed-Tree :
    (y z : node-fiber-Directed-Tree) (e : edge-fiber-Directed-Tree y z) →
    edge-Directed-Tree T
      ( node-inclusion-fiber-Directed-Tree y)
      ( node-inclusion-fiber-Directed-Tree z)
  edge-inclusion-fiber-Directed-Tree =
    edge-inclusion-fiber-Directed-Graph (graph-Directed-Tree T) x

  walk-edge-fiber-Directed-Tree :
    (y z : node-fiber-Directed-Tree) (e : edge-fiber-Directed-Tree y z) →
    walk-node-inclusion-fiber-Directed-Tree y ＝
    cons-walk-Directed-Tree T
      ( edge-inclusion-fiber-Directed-Tree y z e)
      ( walk-node-inclusion-fiber-Directed-Tree z)
  walk-edge-fiber-Directed-Tree =
    walk-edge-fiber-Directed-Graph (graph-Directed-Tree T) x

  graph-fiber-Directed-Tree : Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  graph-fiber-Directed-Tree =
    graph-fiber-Directed-Graph (graph-Directed-Tree T) x

  walk-fiber-Directed-Tree : (y z : node-fiber-Directed-Tree) → UU (l1 ⊔ l2)
  walk-fiber-Directed-Tree =
    walk-fiber-Directed-Graph (graph-Directed-Tree T) x

  walk-to-root-fiber-walk-Directed-Tree :
    (y : node-Directed-Tree T) (w : walk-Directed-Tree T y x) →
    walk-fiber-Directed-Tree (y , w) root-fiber-Directed-Tree
  walk-to-root-fiber-walk-Directed-Tree =
    walk-to-root-fiber-walk-Directed-Graph (graph-Directed-Tree T) x

  walk-to-root-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree) →
    walk-fiber-Directed-Tree y root-fiber-Directed-Tree
  walk-to-root-fiber-Directed-Tree =
    walk-to-root-fiber-Directed-Graph (graph-Directed-Tree T) x
```

### The fiber of `T` at `x`

```agda
  center-unique-direct-successor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree) →
    ( is-root-fiber-Directed-Tree y) +
    ( Σ ( node-fiber-Directed-Tree) ( edge-fiber-Directed-Tree y))
  center-unique-direct-successor-fiber-Directed-Tree =
    center-unique-direct-successor-fiber-Directed-Graph
      ( graph-Directed-Tree T) x

  contraction-unique-direct-successor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree) →
    ( p :
      ( is-root-fiber-Directed-Tree y) +
      ( Σ ( node-fiber-Directed-Tree) (edge-fiber-Directed-Tree y))) →
    center-unique-direct-successor-fiber-Directed-Tree y ＝ p
  contraction-unique-direct-successor-fiber-Directed-Tree =
    contraction-unique-direct-successor-fiber-Directed-Graph
      ( graph-Directed-Tree T) x

  unique-direct-successor-fiber-Directed-Tree :
    unique-direct-successor-Directed-Graph
      ( graph-fiber-Directed-Tree)
      ( root-fiber-Directed-Tree)
  unique-direct-successor-fiber-Directed-Tree =
    unique-direct-successor-fiber-Directed-Graph (graph-Directed-Tree T) x

  is-tree-fiber-Directed-Tree :
    is-tree-Directed-Graph graph-fiber-Directed-Tree
  is-tree-fiber-Directed-Tree =
    is-tree-fiber-Directed-Graph (graph-Directed-Tree T) x

  fiber-Directed-Tree : Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2)
  fiber-Directed-Tree = fiber-Directed-Graph (graph-Directed-Tree T) x

  inclusion-fiber-Directed-Tree : hom-Directed-Tree fiber-Directed-Tree T
  inclusion-fiber-Directed-Tree =
    inclusion-fiber-Directed-Graph (graph-Directed-Tree T) x
```

### Computing the children of a node in a fiber

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2) (x : node-Directed-Tree T)
  where

  direct-predecessor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) → UU (l1 ⊔ l2)
  direct-predecessor-fiber-Directed-Tree =
    direct-predecessor-fiber-Directed-Graph (graph-Directed-Tree T) x

  direct-predecessor-inclusion-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    direct-predecessor-fiber-Directed-Tree y →
    direct-predecessor-Directed-Tree T
      ( node-inclusion-fiber-Directed-Tree T x y)
  direct-predecessor-inclusion-fiber-Directed-Tree =
    direct-predecessor-inclusion-fiber-Directed-Graph (graph-Directed-Tree T) x

  compute-direct-predecessor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    direct-predecessor-fiber-Directed-Tree y ≃
    direct-predecessor-Directed-Tree T
      ( node-inclusion-fiber-Directed-Tree T x y)
  compute-direct-predecessor-fiber-Directed-Tree =
    compute-direct-predecessor-fiber-Directed-Graph (graph-Directed-Tree T) x

  map-compute-direct-predecessor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    direct-predecessor-fiber-Directed-Tree y →
    direct-predecessor-Directed-Tree T
      ( node-inclusion-fiber-Directed-Tree T x y)
  map-compute-direct-predecessor-fiber-Directed-Tree =
    map-compute-direct-predecessor-fiber-Directed-Graph
      ( graph-Directed-Tree T)
      ( x)

  htpy-compute-direct-predecessor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    direct-predecessor-inclusion-fiber-Directed-Tree y ~
    map-compute-direct-predecessor-fiber-Directed-Tree y
  htpy-compute-direct-predecessor-fiber-Directed-Tree =
    htpy-compute-direct-predecessor-fiber-Directed-Graph
      ( graph-Directed-Tree T)
      ( x)

  inv-compute-direct-predecessor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    direct-predecessor-Directed-Tree T
      ( node-inclusion-fiber-Directed-Tree T x y) ≃
    direct-predecessor-fiber-Directed-Tree y
  inv-compute-direct-predecessor-fiber-Directed-Tree =
    inv-compute-direct-predecessor-fiber-Directed-Graph
      ( graph-Directed-Tree T)
      ( x)

  Eq-direct-predecessor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    (u v : direct-predecessor-fiber-Directed-Tree y) → UU (l1 ⊔ l2)
  Eq-direct-predecessor-fiber-Directed-Tree =
    Eq-direct-predecessor-fiber-Directed-Graph (graph-Directed-Tree T) x

  eq-Eq-direct-predecessor-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    ( u v : direct-predecessor-fiber-Directed-Tree y) →
    Eq-direct-predecessor-fiber-Directed-Tree y u v → u ＝ v
  eq-Eq-direct-predecessor-fiber-Directed-Tree =
    eq-Eq-direct-predecessor-fiber-Directed-Graph (graph-Directed-Tree T) x
```

### The fiber of a tree at a base node

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2) (b : base-Directed-Tree T)
  where

  fiber-base-Directed-Tree : Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2)
  fiber-base-Directed-Tree = fiber-Directed-Tree T (node-base-Directed-Tree T b)

  node-fiber-base-Directed-Tree : UU (l1 ⊔ l2)
  node-fiber-base-Directed-Tree = node-Directed-Tree fiber-base-Directed-Tree

  edge-fiber-base-Directed-Tree :
    (x y : node-fiber-base-Directed-Tree) → UU (l1 ⊔ l2)
  edge-fiber-base-Directed-Tree = edge-Directed-Tree fiber-base-Directed-Tree

  root-fiber-base-Directed-Tree : node-fiber-base-Directed-Tree
  root-fiber-base-Directed-Tree = root-Directed-Tree fiber-base-Directed-Tree

  walk-fiber-base-Directed-Tree :
    (x y : node-fiber-base-Directed-Tree) → UU (l1 ⊔ l2)
  walk-fiber-base-Directed-Tree = walk-Directed-Tree fiber-base-Directed-Tree
```

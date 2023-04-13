# Fibers of directed trees

```agda
module trees.fibers-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.directed-graphs

open import trees.directed-trees
```

<details>

## Idea

The fiber of a directed tree `T` at a node `x` consists of all nodes `y` equipped with a walk `w : walk T y x`. An edge from `(y, w)` to `(z , v)` consists of an edge `e : edge T x y` such that `w ＝ cons-walk e v`.

## Definitions

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2) (x : node-Directed-Tree T)
  where

  node-fiber-Directed-Tree : UU (l1 ⊔ l2)
  node-fiber-Directed-Tree =
    Σ (node-Directed-Tree T) (λ y → walk-Directed-Tree T y x)

  module _
    (u : node-fiber-Directed-Tree)
    where

    node-inclusion-fiber-Directed-Tree : node-Directed-Tree T
    node-inclusion-fiber-Directed-Tree = pr1 u

    walk-node-inclusion-fiber-Directed-Tree :
      walk-Directed-Tree T node-inclusion-fiber-Directed-Tree x
    walk-node-inclusion-fiber-Directed-Tree = pr2 u

  edge-fiber-Directed-Tree : (y z : node-fiber-Directed-Tree) → UU (l1 ⊔ l2)
  edge-fiber-Directed-Tree y z =
    Σ ( edge-Directed-Tree T
        ( node-inclusion-fiber-Directed-Tree y)
        ( node-inclusion-fiber-Directed-Tree z))
      ( λ e →
        ( walk-node-inclusion-fiber-Directed-Tree y) ＝
        ( cons-walk-Directed-Tree T e
          ( walk-node-inclusion-fiber-Directed-Tree z)))

  module _
    (y z : node-fiber-Directed-Tree) (e : edge-fiber-Directed-Tree y z)
    where

    edge-inclusion-fiber-Directed-Tree :
      edge-Directed-Tree T
        ( node-inclusion-fiber-Directed-Tree y)
        ( node-inclusion-fiber-Directed-Tree z)
    edge-inclusion-fiber-Directed-Tree = pr1 e

    walk-edge-fiber-Directed-Tree :
      walk-node-inclusion-fiber-Directed-Tree y ＝
      cons-walk-Directed-Tree T
        ( edge-inclusion-fiber-Directed-Tree)
        ( walk-node-inclusion-fiber-Directed-Tree z)
    walk-edge-fiber-Directed-Tree = pr2 e

  graph-fiber-Directed-Tree : Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 graph-fiber-Directed-Tree = node-fiber-Directed-Tree
  pr2 graph-fiber-Directed-Tree = edge-fiber-Directed-Tree
```

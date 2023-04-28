# Fibers of directed trees

```agda
module trees.fibers-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.bases-directed-trees
open import trees.directed-trees
open import trees.morphisms-directed-trees
```

<details>

## Idea

The **fiber** of a directed tree `T` at a node `x` consists of all nodes `y`
equipped with a walk `w : walk T y x`. An edge from `(y, w)` to `(z , v)`
consists of an edge `e : edge T x y` such that `w ＝ cons-walk e v`.

## Definitions

### The underlying graph of the fiber of `T` at `x`

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

  root-fiber-Directed-Tree : node-fiber-Directed-Tree
  pr1 root-fiber-Directed-Tree = x
  pr2 root-fiber-Directed-Tree = refl-walk-Directed-Tree T

  is-root-fiber-Directed-Tree : node-fiber-Directed-Tree → UU (l1 ⊔ l2)
  is-root-fiber-Directed-Tree y = root-fiber-Directed-Tree ＝ y

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

  walk-fiber-Directed-Tree : (y z : node-fiber-Directed-Tree) → UU (l1 ⊔ l2)
  walk-fiber-Directed-Tree = walk-Directed-Graph graph-fiber-Directed-Tree

  walk-to-root-fiber-walk-Directed-Tree :
    (y : node-Directed-Tree T) (w : walk-Directed-Tree T y x) →
    walk-fiber-Directed-Tree (y , w) root-fiber-Directed-Tree
  walk-to-root-fiber-walk-Directed-Tree y refl-walk-Directed-Graph =
    refl-walk-Directed-Graph
  walk-to-root-fiber-walk-Directed-Tree .y
    ( cons-walk-Directed-Graph {y} {z} e w) =
    cons-walk-Directed-Graph
      ( e , refl)
      ( walk-to-root-fiber-walk-Directed-Tree z w)

  walk-to-root-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree) →
    walk-fiber-Directed-Tree y root-fiber-Directed-Tree
  walk-to-root-fiber-Directed-Tree (y , w) =
    walk-to-root-fiber-walk-Directed-Tree y w
```

### The fiber of `T` at `x`

```agda
  center-unique-parent-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree) →
    ( is-root-fiber-Directed-Tree y) +
    ( Σ ( node-fiber-Directed-Tree) ( edge-fiber-Directed-Tree y))
  center-unique-parent-fiber-Directed-Tree (y , refl-walk-Directed-Graph) =
    inl refl
  center-unique-parent-fiber-Directed-Tree
    ( y , cons-walk-Directed-Graph {y} {z} e w) = inr ((z , w) , (e , refl))

  contraction-unique-parent-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree) →
    ( p :
      ( is-root-fiber-Directed-Tree y) +
      ( Σ ( node-fiber-Directed-Tree) (edge-fiber-Directed-Tree y))) →
    center-unique-parent-fiber-Directed-Tree y ＝ p
  contraction-unique-parent-fiber-Directed-Tree ._ (inl refl) = refl
  contraction-unique-parent-fiber-Directed-Tree
    ( y , .(cons-walk-Directed-Graph e v)) (inr ((z , v) , e , refl)) =
    refl

  unique-parent-fiber-Directed-Tree :
    unique-parent-Directed-Graph
      ( graph-fiber-Directed-Tree)
      ( root-fiber-Directed-Tree)
  pr1 (unique-parent-fiber-Directed-Tree y) =
    center-unique-parent-fiber-Directed-Tree y
  pr2 (unique-parent-fiber-Directed-Tree y) =
    contraction-unique-parent-fiber-Directed-Tree y

  is-tree-fiber-Directed-Tree :
    is-tree-Directed-Graph graph-fiber-Directed-Tree
  is-tree-fiber-Directed-Tree =
    is-tree-unique-parent-Directed-Graph
      graph-fiber-Directed-Tree
      root-fiber-Directed-Tree
      unique-parent-fiber-Directed-Tree
      walk-to-root-fiber-Directed-Tree

  fiber-Directed-Tree : Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 fiber-Directed-Tree = graph-fiber-Directed-Tree
  pr2 fiber-Directed-Tree = is-tree-fiber-Directed-Tree

  inclusion-fiber-Directed-Tree :
    hom-Directed-Tree fiber-Directed-Tree T
  pr1 inclusion-fiber-Directed-Tree = node-inclusion-fiber-Directed-Tree
  pr2 inclusion-fiber-Directed-Tree = edge-inclusion-fiber-Directed-Tree
```

### Computing the children of a node in a fiber

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2) (x : node-Directed-Tree T)
  where

  children-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) → UU (l1 ⊔ l2)
  children-fiber-Directed-Tree =
    children-Directed-Tree (fiber-Directed-Tree T x)

  children-inclusion-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    children-fiber-Directed-Tree y →
    children-Directed-Tree T (node-inclusion-fiber-Directed-Tree T x y)
  children-inclusion-fiber-Directed-Tree =
    children-hom-Directed-Tree
      ( fiber-Directed-Tree T x)
      ( T)
      ( inclusion-fiber-Directed-Tree T x)

  compute-children-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    children-fiber-Directed-Tree y ≃
    children-Directed-Tree T (node-inclusion-fiber-Directed-Tree T x y)
  compute-children-fiber-Directed-Tree y =
    ( right-unit-law-Σ-is-contr (λ (u , e) → is-contr-total-path' _)) ∘e
    ( interchange-Σ-Σ _)

  map-compute-children-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    children-fiber-Directed-Tree y →
    children-Directed-Tree T (node-inclusion-fiber-Directed-Tree T x y)
  map-compute-children-fiber-Directed-Tree y =
    map-equiv (compute-children-fiber-Directed-Tree y)

  htpy-compute-children-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    children-inclusion-fiber-Directed-Tree y ~
    map-compute-children-fiber-Directed-Tree y
  htpy-compute-children-fiber-Directed-Tree y t = refl

  inv-compute-children-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    children-Directed-Tree T (node-inclusion-fiber-Directed-Tree T x y) ≃
    children-fiber-Directed-Tree y
  inv-compute-children-fiber-Directed-Tree y =
    inv-equiv (compute-children-fiber-Directed-Tree y)

  Eq-children-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    (u v : children-fiber-Directed-Tree y) → UU (l1 ⊔ l2)
  Eq-children-fiber-Directed-Tree y u v =
    Σ ( pr1 (children-inclusion-fiber-Directed-Tree y u) ＝
        pr1 (children-inclusion-fiber-Directed-Tree y v))
      ( λ p →
        tr
          ( λ t →
            edge-Directed-Tree T t (node-inclusion-fiber-Directed-Tree T x y))
          ( p)
          ( pr2 (children-inclusion-fiber-Directed-Tree y u)) ＝
            pr2 (children-inclusion-fiber-Directed-Tree y v))

  eq-Eq-children-fiber-Directed-Tree :
    (y : node-fiber-Directed-Tree T x) →
    ( u v : children-fiber-Directed-Tree y) →
    Eq-children-fiber-Directed-Tree y u v → u ＝ v
  eq-Eq-children-fiber-Directed-Tree y u v p =
    map-inv-equiv
      ( equiv-ap (compute-children-fiber-Directed-Tree y) u v)
      ( eq-pair-Σ' p)
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

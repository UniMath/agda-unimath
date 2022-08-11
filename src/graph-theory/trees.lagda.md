---
title: Trees
---

```agda
module graph-theory.trees where

open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import graph-theory.paths-undirected-graphs
open import graph-theory.trails-undirected-graphs
open import graph-theory.undirected-graphs
open import graph-theory.walks-undirected-graphs
```

## Idea

A tree is a graph such that the type of trails from x to y is contractible for any two vertices x and y.

## Definition

```agda
is-tree-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
is-tree-Undirected-Graph G =
  (x y : vertex-Undirected-Graph G) → is-contr (trail-Undirected-Graph G x y)

Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Tree l1 l2 = Σ (Undirected-Graph l1 l2) is-tree-Undirected-Graph

module _
  {l1 l2 : Level} (T : Tree l1 l2)
  where

  undirected-graph-Tree : Undirected-Graph l1 l2
  undirected-graph-Tree = pr1 T

  is-tree-undirected-graph-Tree : is-tree-Undirected-Graph undirected-graph-Tree
  is-tree-undirected-graph-Tree = pr2 T

  node-Tree : UU l1
  node-Tree = vertex-Undirected-Graph undirected-graph-Tree

  unordered-pair-nodes-Tree : UU (lsuc lzero ⊔ l1)
  unordered-pair-nodes-Tree =
    unordered-pair-vertices-Undirected-Graph undirected-graph-Tree

  edge-Tree : unordered-pair-nodes-Tree → UU l2
  edge-Tree = edge-Undirected-Graph undirected-graph-Tree
    
  walk-Tree : node-Tree → node-Tree → UU (lsuc lzero ⊔ l1 ⊔ l2)
  walk-Tree = walk-Undirected-Graph undirected-graph-Tree

  is-node-on-walk-Tree :
    {x y : node-Tree} (w : walk-Tree x y) → node-Tree → UU l1
  is-node-on-walk-Tree =
    is-vertex-on-walk-Undirected-Graph undirected-graph-Tree

  node-on-walk-Tree : {x y : node-Tree} → walk-Tree x y → UU l1
  node-on-walk-Tree = vertex-on-walk-Undirected-Graph undirected-graph-Tree

  node-node-on-walk-Tree :
    {x y : node-Tree} (w : walk-Tree x y) → node-on-walk-Tree w → node-Tree
  node-node-on-walk-Tree w = pr1

  is-edge-on-walk-Tree :
    {x y : node-Tree} (w : walk-Tree x y) (p : unordered-pair-nodes-Tree) →
    edge-Tree p → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Tree = is-edge-on-walk-Undirected-Graph undirected-graph-Tree

  edge-on-walk-Tree :
    {x y : node-Tree} → walk-Tree x y → UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-walk-Tree = edge-on-walk-Undirected-Graph undirected-graph-Tree

  edge-edge-on-walk-Tree :
    {x y : node-Tree} (w : walk-Tree x y) →
    edge-on-walk-Tree w → Σ unordered-pair-nodes-Tree edge-Tree
  edge-edge-on-walk-Tree =
    edge-edge-on-walk-Undirected-Graph undirected-graph-Tree

  is-trail-walk-Tree :
    {x y : node-Tree} → walk-Tree x y → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-trail-walk-Tree = is-trail-walk-Undirected-Graph undirected-graph-Tree

  trail-Tree : node-Tree → node-Tree → UU (lsuc lzero ⊔ l1 ⊔ l2)
  trail-Tree = trail-Undirected-Graph undirected-graph-Tree

  walk-trail-Tree : {x y : node-Tree} → trail-Tree x y → walk-Tree x y
  walk-trail-Tree = walk-trail-Undirected-Graph undirected-graph-Tree

  is-trail-walk-trail-Tree :
    {x y : node-Tree} (t : trail-Tree x y) →
    is-trail-walk-Tree (walk-trail-Tree t)
  is-trail-walk-trail-Tree =
    is-trail-walk-trail-Undirected-Graph undirected-graph-Tree

  is-node-on-trail-Tree :
    {x y : node-Tree} (t : trail-Tree x y) → node-Tree → UU l1
  is-node-on-trail-Tree =
    is-vertex-on-trail-Undirected-Graph undirected-graph-Tree

  node-on-trail-Tree : {x y : node-Tree} → trail-Tree x y → UU l1
  node-on-trail-Tree = vertex-on-trail-Undirected-Graph undirected-graph-Tree

  node-node-on-trail-Tree :
    {x y : node-Tree} (w : trail-Tree x y) → node-on-trail-Tree w → node-Tree
  node-node-on-trail-Tree w = pr1

  is-edge-on-trail-Tree :
    {x y : node-Tree} (w : trail-Tree x y) (p : unordered-pair-nodes-Tree) →
    edge-Tree p → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-trail-Tree =
    is-edge-on-trail-Undirected-Graph undirected-graph-Tree

  edge-on-trail-Tree :
    {x y : node-Tree} → trail-Tree x y → UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-trail-Tree = edge-on-trail-Undirected-Graph undirected-graph-Tree

  edge-edge-on-trail-Tree :
    {x y : node-Tree} (w : trail-Tree x y) →
    edge-on-trail-Tree w → Σ unordered-pair-nodes-Tree edge-Tree
  edge-edge-on-trail-Tree =
    edge-edge-on-trail-Undirected-Graph undirected-graph-Tree

  is-path-walk-Tree :
    {x y : node-Tree} → walk-Tree x y → UU l1
  is-path-walk-Tree = is-path-walk-Undirected-Graph undirected-graph-Tree

  path-Tree : node-Tree → node-Tree → UU (lsuc lzero ⊔ l1 ⊔ l2)
  path-Tree = path-Undirected-Graph undirected-graph-Tree

  walk-path-Tree : {x y : node-Tree} → path-Tree x y → walk-Tree x y
  walk-path-Tree = walk-path-Undirected-Graph undirected-graph-Tree

  standard-trail-Tree :
    (x y : node-Tree) → trail-Tree x y
  standard-trail-Tree x y = center (pr2 T x y)

  standard-walk-Tree : (x y : node-Tree) → walk-Tree x y
  standard-walk-Tree x y = walk-trail-Tree (standard-trail-Tree x y)

  is-trail-standard-walk-Tree :
    {x y : node-Tree} → is-trail-walk-Tree (standard-walk-Tree x y)
  is-trail-standard-walk-Tree {x} {y} =
    is-trail-walk-trail-Tree (standard-trail-Tree x y)

  length-walk-Tree : {x y : node-Tree} → walk-Tree x y → ℕ
  length-walk-Tree = length-walk-Undirected-Graph undirected-graph-Tree

  length-trail-Tree : {x y : node-Tree} → trail-Tree x y → ℕ
  length-trail-Tree = length-trail-Undirected-Graph undirected-graph-Tree

  is-constant-walk-Tree-Prop :
    {x y : node-Tree} → walk-Tree x y → UU-Prop lzero
  is-constant-walk-Tree-Prop =
    is-constant-walk-Undirected-Graph-Prop undirected-graph-Tree

  is-constant-walk-Tree : {x y : node-Tree} → walk-Tree x y → UU lzero
  is-constant-walk-Tree =
    is-constant-walk-Undirected-Graph undirected-graph-Tree

  is-decidable-is-constant-walk-Tree :
    {x y : node-Tree} (w : walk-Tree x y) →
    is-decidable (is-constant-walk-Tree w)
  is-decidable-is-constant-walk-Tree =
    is-decidable-is-constant-walk-Undirected-Graph undirected-graph-Tree

  is-constant-trail-Tree-Prop :
    {x y : node-Tree} → trail-Tree x y → UU-Prop lzero
  is-constant-trail-Tree-Prop =
    is-constant-trail-Undirected-Graph-Prop undirected-graph-Tree

  is-constant-trail-Tree : {x y : node-Tree} → trail-Tree x y → UU lzero
  is-constant-trail-Tree =
    is-constant-trail-Undirected-Graph undirected-graph-Tree

  is-decidable-is-constant-trail-Tree :
    {x y : node-Tree} (t : trail-Tree x y) →
    is-decidable (is-constant-trail-Tree t)
  is-decidable-is-constant-trail-Tree =
    is-decidable-is-constant-trail-Undirected-Graph undirected-graph-Tree
```

### Distance between nodes of a tree

```agda
  dist-Tree : node-Tree → node-Tree → ℕ
  dist-Tree x y = length-trail-Tree (standard-trail-Tree x y)
```

## Properties

### Trees are acyclic graphs

```agda
module _
  {l1 l2 : Level} (T : Tree l1 l2)
  where
  
  is-refl-is-circuit-walk-Tree :
    {x y : node-Tree T} (t : trail-Tree T x y) (p : x ＝ y) →
    tr (walk-Tree T x) p refl-walk-Undirected-Graph ＝ walk-trail-Tree T t
  is-refl-is-circuit-walk-Tree {x} t refl =
    ap
      ( walk-trail-Tree T)
      ( eq-is-contr
        ( is-tree-undirected-graph-Tree T x x)
        { pair
          ( refl-walk-Undirected-Graph)
          ( is-trail-refl-walk-Undirected-Graph (undirected-graph-Tree T) {x})}
        { t})

  is-empty-edge-on-walk-is-circuit-walk-Tree :
    {x y : node-Tree T} (t : trail-Tree T x y) →
    (p : x ＝ y) → is-empty (edge-on-trail-Tree T t)
  is-empty-edge-on-walk-is-circuit-walk-Tree {x} t refl e =
    is-empty-edge-on-walk-refl-walk-Undirected-Graph
      ( undirected-graph-Tree T)
      ( x)
      ( tr
        ( edge-on-walk-Tree T)
        ( inv (is-refl-is-circuit-walk-Tree t refl))
        ( e))
```

### If `x` and `y` are merely equal vertices, then the standard trail between them is constant

```agda
module _
  {l1 l2 : Level} (T : Tree l1 l2) {x : node-Tree T}
  where

  is-constant-standard-trail-eq-Tree :
    {y : node-Tree T} →
    (x ＝ y) → is-constant-trail-Tree T (standard-trail-Tree T x y)
  is-constant-standard-trail-eq-Tree {y} refl =
    inv
      ( ap
        ( length-walk-Tree T)
        ( is-refl-is-circuit-walk-Tree T
        ( standard-trail-Tree T x y)
        ( refl)))

  is-constant-standard-trail-mere-eq-Tree :
    {y : node-Tree T} →
    mere-eq x y → is-constant-trail-Tree T (standard-trail-Tree T x y)
  is-constant-standard-trail-mere-eq-Tree {y} H =
    apply-universal-property-trunc-Prop H
      ( is-constant-trail-Tree-Prop T (standard-trail-Tree T x y))
      ( is-constant-standard-trail-eq-Tree)

  eq-is-constant-standard-trail-Tree :
    {y : node-Tree T} →
    is-constant-trail-Tree T (standard-trail-Tree T x y) → x ＝ y
  eq-is-constant-standard-trail-Tree {y} H =
    eq-constant-walk-Undirected-Graph
      ( undirected-graph-Tree T)
      ( pair (standard-walk-Tree T x y) H)
```

### The type of nodes of a tree is a set

```agda
module _
  {l1 l2 : Level} (T : Tree l1 l2) {x : node-Tree T}
  where

  is-set-node-Tree : is-set (node-Tree T)
  is-set-node-Tree =
    is-set-mere-eq-in-id
      ( λ x y H →
        eq-constant-walk-Undirected-Graph
          ( undirected-graph-Tree T)
          ( pair
            ( standard-walk-Tree T x y)
            ( is-constant-standard-trail-mere-eq-Tree T H)))

  node-Tree-Set : UU-Set l1
  pr1 node-Tree-Set = node-Tree T
  pr2 node-Tree-Set = is-set-node-Tree
```

### The type of nodes of a tree has decidable equality

```agda
has-decidable-equality-node-Tree :
  {l1 l2 : Level} (T : Tree l2 l1) → has-decidable-equality (node-Tree T)
has-decidable-equality-node-Tree T x y =
  is-decidable-iff
    ( eq-is-constant-standard-trail-Tree T)
    ( is-constant-standard-trail-eq-Tree T)
    ( is-decidable-is-constant-trail-Tree T (standard-trail-Tree T x y))
```


### Any trail in a tree is a path

-- ```agda
-- module _
--   {l1 l2 : Level} (T : Tree l1 l2)
--   where

--   is-path-is-trail-walk-Tree :
--     {x y : node-Tree T} (w : walk-Tree T x y) →
--     is-trail-walk-Tree T w → is-path-walk-Tree T w
--   is-path-is-trail-walk-Tree {x} {y} w H {pair u KU} {pair v K} p with
--     is-vertex-on-first-or-second-segment-walk-Undirected-Graph
--       (undirected-graph-Tree T) w (pair u KU) (pair v K)
--   ... | inl L = {!!}
--     where
--     w1' : walk-Tree T x u
--     w1' =
--       first-segment-walk-Undirected-Graph (undirected-graph-Tree T) w (pair u KU)
--     w1 : walk-Tree T x v
--     w1 =
--       first-segment-walk-Undirected-Graph
--         ( undirected-graph-Tree T)
--         ( w1')
--         ( pair v L)
--     w' : walk-Tree T v u
--     w' = {!!}
--   ... | inr L = {!!}
--     where
--     w1 : walk-Tree T x u
--     w1 =
--       first-segment-walk-Undirected-Graph (undirected-graph-Tree T) w (pair u KU)

-- {-
--     where
--     w1 : walk-Tree T x (node-node-on-walk-Tree T w u)
--     w1 =
--       first-segment-walk-Undirected-Graph (undirected-graph-Tree T) w u
--     w2' : walk-Tree T (node-node-on-walk-Tree T w u) y
--     w2' =
--       second-segment-walk-Undirected-Graph (undirected-graph-Tree T) w u
--     w2 : walk-Tree T (node-node-on-walk-Tree T w u) (node-node-on-walk-Tree T w v)
--     w2 = {!first-segment-walk-Undirected-Graph (undirected-graph-Tree T) w2' !}
--   -}
-- ```

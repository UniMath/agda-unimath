---
title: Trees
---

```agda
module graph-theory.trees where

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
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

  walk-Tree : node-Tree → node-Tree → UU (lsuc lzero ⊔ l1 ⊔ l2)
  walk-Tree = walk-Undirected-Graph undirected-graph-Tree

  node-on-walk-Tree : {x y : node-Tree} → walk-Tree x y → UU l1
  node-on-walk-Tree = vertex-on-walk-Undirected-Graph undirected-graph-Tree

  node-node-on-walk-Tree :
    {x y : node-Tree} (w : walk-Tree x y) → node-on-walk-Tree w → node-Tree
  node-node-on-walk-Tree w = pr1

  edge-on-walk-Tree :
    {x y : node-Tree} → walk-Tree x y → UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-walk-Tree = edge-on-walk-Undirected-Graph undirected-graph-Tree

  is-trail-walk-Tree :
    {x y : node-Tree} → walk-Tree x y → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-trail-walk-Tree = is-trail-walk-Undirected-Graph undirected-graph-Tree

  trail-Tree : node-Tree → node-Tree → UU (lsuc lzero ⊔ l1 ⊔ l2)
  trail-Tree = trail-Undirected-Graph undirected-graph-Tree

  walk-trail-Tree : {x y : node-Tree} → trail-Tree x y → walk-Tree x y
  walk-trail-Tree = walk-trail-Undirected-Graph undirected-graph-Tree

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
```

## Properties

### Trees are acyclic graphs

```agda
module _
  {l1 l2 : Level} (T : Tree l1 l2)
  where
  
  is-refl-is-circuit-walk-Tree :
    {x y : node-Tree T} (w : walk-Tree T x y) → is-trail-walk-Tree T w →
    (p : x ＝ y) → tr (walk-Tree T x) p refl-walk-Undirected-Graph ＝ w
  is-refl-is-circuit-walk-Tree {x} w H refl =
    ap
      ( walk-trail-Tree T)
      ( eq-is-contr
        ( is-tree-undirected-graph-Tree T x x)
        { pair
          ( refl-walk-Undirected-Graph)
          ( is-trail-refl-walk-Undirected-Graph (undirected-graph-Tree T) {x})}
        { pair w H})

  is-empty-edge-on-walk-is-circuit-walk-Tree :
    {x y : node-Tree T} (w : walk-Tree T x y) → is-trail-walk-Tree T w →
    (p : x ＝ y) → is-empty (edge-on-walk-Tree T w)
  is-empty-edge-on-walk-is-circuit-walk-Tree {x} w H refl e =
    is-empty-edge-on-walk-refl-walk-Undirected-Graph
      ( undirected-graph-Tree T)
      ( x)
      ( tr
        ( edge-on-walk-Tree T)
        ( inv (is-refl-is-circuit-walk-Tree w H refl))
        ( e))
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

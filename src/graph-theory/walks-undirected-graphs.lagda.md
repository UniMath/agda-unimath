# Walks in undirected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.walks-undirected-graphs where

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs
```

## Idea

A walk in an undirected graph consists of a list of edges that connect the starting point with the end point. Walks may repeat edges and pass through the same vertex multiple times.

## Definitions

### Walks in undirected graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  data
    walk-Undirected-Graph (x : vertex-Undirected-Graph G) :
      vertex-Undirected-Graph G → UU (l1 ⊔ l2 ⊔ lsuc lzero)
      where
      refl-walk-Undirected-Graph : walk-Undirected-Graph x x
      cons-walk-Undirected-Graph :
        (p : unordered-pair (vertex-Undirected-Graph G)) →
        (e : edge-Undirected-Graph G p) →
        {y : type-unordered-pair p} →
        walk-Undirected-Graph x (element-unordered-pair p y) →
        walk-Undirected-Graph x (other-element-unordered-pair p y)
```

### The vertices on a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-Undirected-Graph G → UU l1
  is-vertex-on-walk-Undirected-Graph refl-walk-Undirected-Graph v = x ＝ v
  is-vertex-on-walk-Undirected-Graph (cons-walk-Undirected-Graph p e {y} w) v =
    ( is-vertex-on-walk-Undirected-Graph w v) +
    ( other-element-unordered-pair p y ＝ v)

  vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) → UU l1
  vertex-on-walk-Undirected-Graph w =
    Σ (vertex-Undirected-Graph G) (is-vertex-on-walk-Undirected-Graph w)
```

### Concatenating walks

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  concat-walk-Undirected-Graph :
    {y z : vertex-Undirected-Graph G} →
    walk-Undirected-Graph G x y → walk-Undirected-Graph G y z →
    walk-Undirected-Graph G x z
  concat-walk-Undirected-Graph w refl-walk-Undirected-Graph = w
  concat-walk-Undirected-Graph w (cons-walk-Undirected-Graph p e v) =
    cons-walk-Undirected-Graph p e (concat-walk-Undirected-Graph w v)
```

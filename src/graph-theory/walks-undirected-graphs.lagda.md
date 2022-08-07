# Walks in undirected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.walks-undirected-graphs where

open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.standard-finite-types
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

  vertex-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-on-walk-Undirected-Graph w → vertex-Undirected-Graph G
  vertex-vertex-on-walk-Undirected-Graph w = pr1
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

### The length of a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  length-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} → walk-Undirected-Graph G x y → ℕ
  length-walk-Undirected-Graph refl-walk-Undirected-Graph = 0
  length-walk-Undirected-Graph (cons-walk-Undirected-Graph p e w) =
    succ-ℕ (length-walk-Undirected-Graph w)

  compute-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-on-walk-Undirected-Graph G w ≃
    Fin (succ-ℕ (length-walk-Undirected-Graph w))
  compute-vertex-on-walk-Undirected-Graph refl-walk-Undirected-Graph =
    equiv-is-contr
      ( is-contr-total-path x)
      ( is-contr-Fin-one-ℕ)
  compute-vertex-on-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e {y} w) =
    ( equiv-coprod
      ( compute-vertex-on-walk-Undirected-Graph w)
      ( equiv-is-contr
        ( is-contr-total-path (other-element-unordered-pair p y))
        ( is-contr-unit))) ∘e
    ( left-distributive-Σ-coprod
      ( vertex-Undirected-Graph G)
      ( is-vertex-on-walk-Undirected-Graph G w)
      ( λ z → other-element-unordered-pair p y ＝ z))
```

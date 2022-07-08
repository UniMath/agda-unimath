---
title: Stabilizers of concrete group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.stabilizers-concrete-group-actions where

open import foundation.dependent-pair-types
open import foundation.connected-components
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.concrete-group-actions
open import group-theory.orbits-concrete-group-actions
```

## Idea

The stabilizer of an element `x : X pt` of a concrete G-set `X : BG → UU-Set` is the connected component of `pair pt x` in the type of orbits of `X`. Its loop space is indeed the type of elements `g : G` such that `g x = x`.

## Definition

```agda
stabilizer-Concrete-Group-Action :
  {l1 l2 : Level} (G : Concrete-Group l1)
  (X : action-Concrete-Group l2 G) → type-action-Concrete-Group G X →
  UU (l1 ⊔ l2)
stabilizer-Concrete-Group-Action G X x =
  connected-component
    ( orbit-action-Concrete-Group G X)
    ( pair (shape-Concrete-Group G) x)
```

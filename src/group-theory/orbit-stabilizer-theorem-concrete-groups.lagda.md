---
title: The orbit-stabilizer theorem for concrete groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.orbit-stabilizer-theorem-concrete-groups where

open import foundation.dependent-pair-types
open import foundation.mere-equality
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
```

## Idea

The orbit stabilizer theorem for concrete groups asserts that the type `Orbit(x)` of orbits of an element `x : X *` is deloopable and fits in a fiber sequence

```md
  BG_x ----> BG ----> B(Orbit(x))
```

To see that this is indeed a formulation of the orbit-stabilizer theorem, note that the delooping of `Orbit(x)` gives `Orbit(x)` the structure of a group. Furthermore, this fiber sequence induces a short exact sequence

```md
  G_x ----> G ----> Orbit(x),
```

which induces a bijection from the cosets of the stabilizer subgroup `G_x` of `G` to the type `Orbit(x)`.

## Definitions

```agda
coset-stabilizer-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  type-action-Concrete-Group G X → action-Concrete-Group (l1 ⊔ l2) G
coset-stabilizer-action-Concrete-Group G X x u =
  subset-Set
    ( X u)
    ( λ y → mere-eq-Prop (pair (shape-Concrete-Group G) x) (pair u y))
```

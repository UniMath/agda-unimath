---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.ideals where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.abelian-subgroups

open import ring-theory.rings
open import ring-theory.subsets-rings
```

## Idea

A left ideal of a ring `R` is an additive subgroup of `R` that is closed under multiplication by elements of `R` from the left.

## Definitions

### Additive subgroups

```agda
is-additive-subgroup-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-additive-subgroup-subset-Ring R = is-subgroup-Ab (ab-Ring R)
```

### Left ideals

```agda
is-closed-under-mul-left-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-closed-under-mul-left-subset-Ring R P =
  (x : type-Ring R) (y : type-Ring R) →
  type-Prop (P y) → type-Prop (P (mul-Ring R x y))

is-left-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-left-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  is-closed-under-mul-left-subset-Ring R P

Left-Ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
Left-Ideal-Ring l R = Σ (subset-Ring l R) (is-left-ideal-subset-Ring R)
```

### Right ideals

```agda
is-closed-under-mul-right-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-closed-under-mul-right-subset-Ring R P =
  (x : type-Ring R) (y : type-Ring R) →
  type-Prop (P x) → type-Prop (P (mul-Ring R x y))

is-right-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-right-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  is-closed-under-mul-right-subset-Ring R P

Right-Ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
Right-Ideal-Ring l R = Σ (subset-Ring l R) (is-right-ideal-subset-Ring R)
```

### Two-sided ideals

```agda
is-two-sided-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-two-sided-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  ( is-closed-under-mul-left-subset-Ring R P ×
    is-closed-under-mul-right-subset-Ring R P)

Two-Sided-Ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
Two-Sided-Ideal-Ring l R =
  Σ (subset-Ring l R) (is-two-sided-ideal-subset-Ring R)
```

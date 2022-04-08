---
title: Ideals in rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.ideals-rings where

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.abelian-subgroups

open import ring-theory.rings
open import ring-theory.subsets-rings

open import univalent-combinatorics.lists
```

## Idea

A left ideal of a ring `R` is an additive subgroup of `R` that is closed under multiplication by elements of `R` from the left.

## Definitions

### Additive subgroups

```agda
module _
  {l1 : Level} (R : Ring l1)
  where
  
  is-additive-subgroup-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-additive-subgroup-subset-Ring = is-subgroup-Ab (ab-Ring R)
```

### Left ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where
  
  is-closed-under-mul-left-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-closed-under-mul-left-subset-Ring P =
    (x : type-Ring R) (y : type-Ring R) →
    type-Prop (P y) → type-Prop (P (mul-Ring R x y))
  
  is-left-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-left-ideal-subset-Ring P =
    is-additive-subgroup-subset-Ring R P ×
    is-closed-under-mul-left-subset-Ring P
  
left-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
left-ideal-Ring l R = Σ (subset-Ring l R) (is-left-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  subset-left-ideal-Ring : subset-Ring l2 R
  subset-left-ideal-Ring = pr1 I

  type-left-ideal-Ring : UU (l1 ⊔ l2)
  type-left-ideal-Ring = type-subset-Ring R subset-left-ideal-Ring

  inclusion-left-ideal-Ring : type-left-ideal-Ring → type-Ring R
  inclusion-left-ideal-Ring = inclusion-subset-Ring R subset-left-ideal-Ring

  is-left-ideal-subset-left-ideal-Ring :
    is-left-ideal-subset-Ring R subset-left-ideal-Ring
  is-left-ideal-subset-left-ideal-Ring = pr2 I

  is-additive-subgroup-subset-left-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-left-ideal-Ring
  is-additive-subgroup-subset-left-ideal-Ring =
    pr1 is-left-ideal-subset-left-ideal-Ring

  is-closed-under-mul-left-ideal-Ring :
    is-closed-under-mul-left-subset-Ring R subset-left-ideal-Ring
  is-closed-under-mul-left-ideal-Ring =
    pr2 is-left-ideal-subset-left-ideal-Ring
```

### Right ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where
  
  is-closed-under-mul-right-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-closed-under-mul-right-subset-Ring P =
    (x : type-Ring R) (y : type-Ring R) →
    type-Prop (P x) → type-Prop (P (mul-Ring R x y))

  is-right-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-right-ideal-subset-Ring P =
    is-additive-subgroup-subset-Ring R P ×
    is-closed-under-mul-right-subset-Ring P

right-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
right-ideal-Ring l R = Σ (subset-Ring l R) (is-right-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : right-ideal-Ring l2 R)
  where

  subset-right-ideal-Ring : subset-Ring l2 R
  subset-right-ideal-Ring = pr1 I

  type-right-ideal-Ring : UU (l1 ⊔ l2)
  type-right-ideal-Ring = type-subset-Ring R subset-right-ideal-Ring

  inclusion-right-ideal-Ring : type-right-ideal-Ring → type-Ring R
  inclusion-right-ideal-Ring = inclusion-subset-Ring R subset-right-ideal-Ring

  is-right-ideal-subset-right-ideal-Ring :
    is-right-ideal-subset-Ring R subset-right-ideal-Ring
  is-right-ideal-subset-right-ideal-Ring = pr2 I

  is-additive-subgroup-subset-right-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-right-ideal-Ring
  is-additive-subgroup-subset-right-ideal-Ring =
    pr1 is-right-ideal-subset-right-ideal-Ring

  is-closed-under-mul-right-ideal-Ring :
    is-closed-under-mul-right-subset-Ring R subset-right-ideal-Ring
  is-closed-under-mul-right-ideal-Ring =
    pr2 is-right-ideal-subset-right-ideal-Ring
```

### Two-sided ideals

```agda
is-two-sided-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-two-sided-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  ( is-closed-under-mul-left-subset-Ring R P ×
    is-closed-under-mul-right-subset-Ring R P)

two-sided-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
two-sided-ideal-Ring l R =
  Σ (subset-Ring l R) (is-two-sided-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : two-sided-ideal-Ring l2 R)
  where

  subset-two-sided-ideal-Ring : subset-Ring l2 R
  subset-two-sided-ideal-Ring = pr1 I

  type-two-sided-ideal-Ring : UU (l1 ⊔ l2)
  type-two-sided-ideal-Ring = type-subset-Ring R subset-two-sided-ideal-Ring

  inclusion-two-sided-ideal-Ring : type-two-sided-ideal-Ring → type-Ring R
  inclusion-two-sided-ideal-Ring =
    inclusion-subset-Ring R subset-two-sided-ideal-Ring

  is-two-sided-ideal-subset-two-sided-ideal-Ring :
    is-two-sided-ideal-subset-Ring R subset-two-sided-ideal-Ring
  is-two-sided-ideal-subset-two-sided-ideal-Ring = pr2 I

  is-additive-subgroup-subset-two-sided-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-two-sided-ideal-Ring
  is-additive-subgroup-subset-two-sided-ideal-Ring =
    pr1 is-two-sided-ideal-subset-two-sided-ideal-Ring

  is-closed-under-mul-left-two-sided-ideal-Ring :
    is-closed-under-mul-left-subset-Ring R subset-two-sided-ideal-Ring
  is-closed-under-mul-left-two-sided-ideal-Ring =
    pr1 (pr2 is-two-sided-ideal-subset-two-sided-ideal-Ring)

  is-closed-under-mul-right-two-sided-ideal-Ring :
    is-closed-under-mul-right-subset-Ring R subset-two-sided-ideal-Ring
  is-closed-under-mul-right-two-sided-ideal-Ring =
    pr2 (pr2 is-two-sided-ideal-subset-two-sided-ideal-Ring)
```

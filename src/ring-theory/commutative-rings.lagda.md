---
title: Commutative rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.commutative-rings where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using (is-prop; is-prop-Π)
open import foundation.universe-levels using (Level; UU; lsuc)

open import ring-theory.rings using
  ( Ring; type-Ring; mul-Ring; is-set-type-Ring; zero-Ring; add-Ring; neg-Ring)
```

## Idea

A ring `R` is said to be commutative if its multiplicative operation is commutative, i.e., if `xy = yx` for all `x, y ∈ R`.

## Definition

```agda
is-commutative-Ring :
  { l : Level} → Ring l → UU l
is-commutative-Ring R =
  (x y : type-Ring R) → Id (mul-Ring R x y) (mul-Ring R y x)

is-prop-is-commutative-Ring :
  { l : Level} (R : Ring l) → is-prop (is-commutative-Ring R)
is-prop-is-commutative-Ring R =
  is-prop-Π
    ( λ x →
      is-prop-Π
      ( λ y →
        is-set-type-Ring R (mul-Ring R x y) (mul-Ring R y x)))

Comm-Ring :
  ( l : Level) → UU (lsuc l)
Comm-Ring l = Σ (Ring l) is-commutative-Ring

module _
  {l : Level} (R : Comm-Ring l)
  where
  
  ring-Comm-Ring : Ring l
  ring-Comm-Ring = pr1 R

  is-commutative-Comm-Ring : is-commutative-Ring ring-Comm-Ring
  is-commutative-Comm-Ring = pr2 R

  type-Comm-Ring : UU l
  type-Comm-Ring = type-Ring ring-Comm-Ring

  zero-Comm-Ring : type-Comm-Ring
  zero-Comm-Ring = zero-Ring ring-Comm-Ring

  add-Comm-Ring : type-Comm-Ring → type-Comm-Ring → type-Comm-Ring
  add-Comm-Ring = add-Ring ring-Comm-Ring

  neg-Comm-Ring : type-Comm-Ring → type-Comm-Ring
  neg-Comm-Ring = neg-Ring ring-Comm-Ring
```

---
title: Commutative rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module commutative-algebra.commutative-rings where

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

Commutative-Ring :
  ( l : Level) → UU (lsuc l)
Commutative-Ring l = Σ (Ring l) is-commutative-Ring

module _
  {l : Level} (R : Commutative-Ring l)
  where
  
  ring-Commutative-Ring : Ring l
  ring-Commutative-Ring = pr1 R

  is-commutative-Commutative-Ring : is-commutative-Ring ring-Commutative-Ring
  is-commutative-Commutative-Ring = pr2 R

  type-Commutative-Ring : UU l
  type-Commutative-Ring = type-Ring ring-Commutative-Ring

  zero-Commutative-Ring : type-Commutative-Ring
  zero-Commutative-Ring = zero-Ring ring-Commutative-Ring

  add-Commutative-Ring : type-Commutative-Ring → type-Commutative-Ring → type-Commutative-Ring
  add-Commutative-Ring = add-Ring ring-Commutative-Ring

  neg-Commutative-Ring : type-Commutative-Ring → type-Commutative-Ring
  neg-Commutative-Ring = neg-Ring ring-Commutative-Ring

  mul-Commutative-Ring : (x y : type-Commutative-Ring) → type-Commutative-Ring
  mul-Commutative-Ring = mul-Ring ring-Commutative-Ring
```

# Commutative rings

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.commutative-rings where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using (is-prop; is-prop-Π)
open import foundation.universe-levels using (Level; UU; lsuc)

open import ring-theory.rings using
  ( Ring; type-Ring; mul-Ring; is-set-type-Ring)
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

ring-Comm-Ring :
  { l : Level} → Comm-Ring l → Ring l
ring-Comm-Ring = pr1

is-commutative-Comm-Ring :
  { l : Level} (R : Comm-Ring l) → is-commutative-Ring (ring-Comm-Ring R)
is-commutative-Comm-Ring = pr2
```

---
title: Prime ideals in commutative rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module commutative-algebra.prime-ideals-commutative-rings where

open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositions
open import foundation.universe-levels
```

## Idea

A prime ideal is an ideal `I` in a commutative ring `R` such that for every `a,b : R` whe have `ab ∈ I ⇒ (a ∈ I) ∨ (b ∈ I)`.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 R)
  where
  
  is-prime-ideal-commutative-ring-Prop : UU-Prop (l1 ⊔ l2)
  is-prime-ideal-commutative-ring-Prop =
    Π-Prop
      ( type-Commutative-Ring R)
      ( λ a →
        Π-Prop
          ( type-Commutative-Ring R)
          ( λ b →
            function-Prop
              ( is-in-ideal-Commutative-Ring R I (mul-Commutative-Ring R a b))
              ( disj-Prop
                ( subset-ideal-Commutative-Ring R I a)
                ( subset-ideal-Commutative-Ring R I b))))

  is-prime-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  is-prime-ideal-Commutative-Ring =
    type-Prop is-prime-ideal-commutative-ring-Prop

  is-prop-is-prime-ideal-Commutative-Ring :
    is-prop is-prime-ideal-Commutative-Ring
  is-prop-is-prime-ideal-Commutative-Ring =
    is-prop-type-Prop is-prime-ideal-commutative-ring-Prop

prime-ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
prime-ideal-Commutative-Ring l2 R =
  Σ (ideal-Commutative-Ring l2 R) (is-prime-ideal-Commutative-Ring R)

module _
  {l1 l2 : Level} (R : Commutative-Ring l1)
  (P : prime-ideal-Commutative-Ring l2 R)
  where

  ideal-prime-ideal-Commutative-Ring : ideal-Commutative-Ring l2 R
  ideal-prime-ideal-Commutative-Ring = pr1 P

  is-prime-ideal-ideal-prime-ideal-Commutative-Ring :
    is-prime-ideal-Commutative-Ring R ideal-prime-ideal-Commutative-Ring
  is-prime-ideal-ideal-prime-ideal-Commutative-Ring = pr2 P
```

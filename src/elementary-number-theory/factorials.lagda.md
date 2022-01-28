---
title: Univalent Mathematics in Agda
---

# Factorials of natural numbers

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.factorials where

open import elementary-number-theory.divisibility-natural-numbers using
  ( div-ℕ; transitive-div-ℕ)
open import elementary-number-theory.equality-natural-numbers using (Eq-eq-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; decide-leq-succ-ℕ; leq-zero-ℕ; leq-mul-is-nonzero-ℕ')
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; commutative-mul-ℕ; is-nonzero-mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-ℕ; is-nonzero-succ-ℕ)
open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.identity-types using (refl)
```

# Factorials

```agda
factorial-ℕ : ℕ → ℕ
factorial-ℕ 0 = 1
factorial-ℕ (succ-ℕ m) = mul-ℕ (factorial-ℕ m) (succ-ℕ m)
```

```agda
div-factorial-ℕ :
  (n x : ℕ) → leq-ℕ x n → is-nonzero-ℕ x → div-ℕ x (factorial-ℕ n)
div-factorial-ℕ zero-ℕ zero-ℕ l H = ex-falso (H refl)
div-factorial-ℕ (succ-ℕ n) x l H with
  decide-leq-succ-ℕ x n l
... | inl l' =
  transitive-div-ℕ x
    ( factorial-ℕ n)
    ( factorial-ℕ (succ-ℕ n))
    ( div-factorial-ℕ n x l' H)
    ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (factorial-ℕ n)))
... | inr refl = pair (factorial-ℕ n) refl
```

```agda
is-nonzero-factorial-ℕ :
  (x : ℕ) → is-nonzero-ℕ (factorial-ℕ x)
is-nonzero-factorial-ℕ zero-ℕ = Eq-eq-ℕ
is-nonzero-factorial-ℕ (succ-ℕ x) =
  is-nonzero-mul-ℕ
    ( factorial-ℕ x)
    ( succ-ℕ x)
    ( is-nonzero-factorial-ℕ x)
    ( is-nonzero-succ-ℕ x)

leq-factorial-ℕ :
  (n : ℕ) → leq-ℕ n (factorial-ℕ n)
leq-factorial-ℕ zero-ℕ = leq-zero-ℕ 1
leq-factorial-ℕ (succ-ℕ n) =
  leq-mul-is-nonzero-ℕ'
    ( factorial-ℕ n)
    ( succ-ℕ n)
    ( is-nonzero-factorial-ℕ n)
```

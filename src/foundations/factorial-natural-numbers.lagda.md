---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.factorial-natural-numbers where

open import foundations.coproduct-types using (inl; inr)
open import foundations.dependent-pair-types using (pair; pr1; pr2)
open import foundations.divisibility-natural-numbers using
  ( div-ℕ; transitive-div-ℕ)
open import foundations.empty-type using (ex-falso)
open import foundations.identity-types using (refl)
open import foundations.inequality-natural-numbers using
  ( leq-ℕ; decide-leq-succ-ℕ)
open import foundations.multiplication-natural-numbers using
  ( mul-ℕ; commutative-mul-ℕ)
open import foundations.natural-numbers using (ℕ; zero-ℕ; succ-ℕ; is-nonzero-ℕ)
```

# Factorials

```agda
factorial-ℕ : ℕ → ℕ
factorial-ℕ 0 = 1
factorial-ℕ (succ-ℕ m) = mul-ℕ (factorial-ℕ m) (succ-ℕ m)
```

```agda
div-factorial-is-nonzero-ℕ :
  (n x : ℕ) → leq-ℕ x n → is-nonzero-ℕ x → div-ℕ x (factorial-ℕ n)
div-factorial-is-nonzero-ℕ zero-ℕ zero-ℕ l H = ex-falso (H refl)
div-factorial-is-nonzero-ℕ (succ-ℕ n) x l H with
  decide-leq-succ-ℕ x n l
... | inl l' =
  transitive-div-ℕ x
    ( factorial-ℕ n)
    ( factorial-ℕ (succ-ℕ n))
    ( div-factorial-is-nonzero-ℕ n x l' H)
    ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (factorial-ℕ n)))
... | inr refl = pair (factorial-ℕ n) refl
```

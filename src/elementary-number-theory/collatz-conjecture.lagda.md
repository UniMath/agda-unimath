---
title: Univalent Mathematics in Agda
---

# The Collatz conjecture

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.collatz-conjecture where

open import foundations.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (Σ; pair)
open import foundation.levels using (UU; lzero)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-ℕ; is-one-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( is-decidable-div-ℕ)
```

# We state the collatz conjecture

```agda
collatz : ℕ → ℕ
collatz n with is-decidable-div-ℕ 2 n
... | inl (pair y p) = y
... | inr f = succ-ℕ (mul-ℕ 3 n)

iterate-collatz : ℕ → ℕ → ℕ
iterate-collatz zero-ℕ n = n
iterate-collatz (succ-ℕ k) n = collatz (iterate-collatz k n)

Collatz-conjecture : UU lzero
Collatz-conjecture =
  (n : ℕ) → is-nonzero-ℕ n → Σ ℕ (λ k → is-one-ℕ (iterate-collatz k n))
```

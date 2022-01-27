---
title: Univalent Mathematics in Agda
---

# The Goldbach conjecture

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module elementary-number-theory.goldbach-conjecture where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ)
open import
  elementary-number-theory.divisibility-natural-numbers using (is-even-ℕ)
open import foundation.identity-types using (Id)
open import elementary-number-theory.inequality-natural-numbers using (le-ℕ)
open import foundation.universe-levels using (UU; lzero)
open import elementary-number-theory.natural-numbers using (ℕ)
open import elementary-number-theory.primes-natural-numbers using (is-prime-ℕ)
```

# The Goldbach Conjecture

```agda
Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (le-ℕ 2 n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime-ℕ p) × (Σ ℕ (λ q → (is-prime-ℕ q) × Id (add-ℕ p q) n)))
```

---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.goldbach-conjecture where

open import foundations.addition-natural-numbers using (add-ℕ)
open import foundations.cartesian-product-types using (_×_)
open import foundations.dependent-pair-types using (Σ)
open import foundations.divisibility-natural-numbers using (is-even-ℕ)
open import foundations.identity-types using (Id)
open import foundations.inequality-natural-numbers using (le-ℕ)
open import foundations.levels using (UU; lzero)
open import foundations.natural-numbers using (ℕ)
open import foundations.primes-natural-numbers using (is-prime-ℕ)
```

# The Goldbach Conjecture

```agda
Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (le-ℕ 2 n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime-ℕ p) × (Σ ℕ (λ q → (is-prime-ℕ q) × Id (add-ℕ p q) n)))
```

---
title: The Twin Prime conjecture
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.twin-prime-conjecture where

open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ)
open import elementary-number-theory.prime-numbers using (is-prime-ℕ)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ)
open import foundation.universe-levels using (UU; lzero)
```

# The twin prime conjecture

```agda
is-twin-prime-ℕ : ℕ → UU lzero
is-twin-prime-ℕ n = (is-prime-ℕ n) × (is-prime-ℕ (succ-ℕ (succ-ℕ n)))

{- The twin prime conjecture asserts that there are infinitely many twin
   primes. We assert that there are infinitely twin primes by asserting that
   for every n : ℕ there is a twin prime that is larger than n. -}

twin-prime-conjecture : UU lzero
twin-prime-conjecture =
  (n : ℕ) → Σ ℕ (λ p → (is-twin-prime-ℕ p) × (leq-ℕ n p))
```

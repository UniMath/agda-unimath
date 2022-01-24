---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.proper-divisors-natural-numbers where

open import foundations.cartesian-product-types using (_×_)
open import foundations.decidable-types using
  ( is-decidable; is-decidable-prod; is-decidable-neg)
open import foundations.dependent-pair-types using (pair; pr1; pr2)
open import foundations.divisibility-natural-numbers using
  ( div-ℕ; div-zero-ℕ; leq-div-ℕ)
open import foundations.equality-natural-numbers using
  ( has-decidable-equality-ℕ)
open import foundations.identity-types using (Id)
open import foundations.inequality-natural-numbers using (le-ℕ; le-leq-neq-ℕ)
open import foundations.levels using (UU; lzero)
open import foundations.modular-arithmetic-standard-finite-types using
  (is-decidable-div-ℕ)
open import foundations.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-nonzero-succ-ℕ; is-nonzero-ℕ)
open import foundations.negation using (¬)
```

# Proper divisors of natural numbers

```agda
is-proper-divisor-ℕ : ℕ → ℕ → UU lzero
is-proper-divisor-ℕ n d = ¬ (Id d n) × div-ℕ d n

is-decidable-is-proper-divisor-ℕ :
  (n d : ℕ) → is-decidable (is-proper-divisor-ℕ n d)
is-decidable-is-proper-divisor-ℕ n d =
  is-decidable-prod
    ( is-decidable-neg (has-decidable-equality-ℕ d n))
    ( is-decidable-div-ℕ d n)

is-proper-divisor-zero-succ-ℕ : (n : ℕ) → is-proper-divisor-ℕ zero-ℕ (succ-ℕ n)
pr1 (is-proper-divisor-zero-succ-ℕ n) = is-nonzero-succ-ℕ n
pr2 (is-proper-divisor-zero-succ-ℕ n) = div-zero-ℕ (succ-ℕ n)

le-is-proper-divisor-ℕ :
  (x y : ℕ) → is-nonzero-ℕ y → is-proper-divisor-ℕ y x → le-ℕ x y
le-is-proper-divisor-ℕ x y H K =
  le-leq-neq-ℕ (leq-div-ℕ x y H (pr2 K)) (pr1 K)
```

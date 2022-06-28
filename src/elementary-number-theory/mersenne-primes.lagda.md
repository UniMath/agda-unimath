---
title: Mersenne primes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.mersenne-primes where

open import elementary-number-theory.natural-numbers using (ℕ)
open import elementary-number-theory.distance-natural-numbers using (dist-ℕ)
open import elementary-number-theory.exponentiation-natural-numbers using (exp-ℕ)
open import elementary-number-theory.prime-numbers using (is-prime-ℕ)

open import foundation.dependent-pair-types using (Σ)
open import foundation.cartesian-product-types using (_×_)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

A Mersenne prime is a prime number that is one less than a power of two.

## Definition

```agda
is-mersenne-prime : ℕ → UU lzero
is-mersenne-prime n = is-prime-ℕ n × Σ ℕ (λ k → Id (dist-ℕ (exp-ℕ 2 k) 1) n)

is-mersenne-prime-power : ℕ → UU lzero
is-mersenne-prime-power k = is-prime-ℕ (dist-ℕ (exp-ℕ 2 k) 1)
```

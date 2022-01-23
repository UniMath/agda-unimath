---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.collatz-conjecture where

open import foundations.coproduct-types using (inl; inr)
open import foundations.dependent-pair-types using (pair)
open import foundations.multiplication-natural-numbers using (mul-ℕ)
open import foundations.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import foundations.modular-arithmetic-standard-finite-types using
  ( is-decidable-div-ℕ)
```

# We state the collatz conjecture

```agda
collatz : ℕ → ℕ
collatz n with is-decidable-div-ℕ 2 n
... | inl (pair y p) = y
... | inr f = succ-ℕ (mul-ℕ 3 n)
```

---
title: Products of natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.products-of-natural-numbers where

open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.unit-type

open import univalent-combinatorics.standard-finite-types
```

```agda
Π-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
Π-ℕ zero-ℕ x = 1
Π-ℕ (succ-ℕ k) x = mul-ℕ (Π-ℕ k (λ i → x (inl i))) (x (inr star))
```

---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.equality-integers where

open import foundations.decidable-types using
  ( is-decidable; has-decidable-equality; has-decidable-equality-unit)
open import foundations.equality-coproduct-types using
  ( has-decidable-equality-coprod)
open import foundations.integers using
  ( ℤ; zero-ℤ; is-zero-ℤ; one-ℤ; is-one-ℤ; neg-one-ℤ; is-neg-one-ℤ)
open import foundations.natural-numbers using
  ( has-decidable-equality-ℕ)
```

# The identity type of the integers

```agda
has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ =
  has-decidable-equality-coprod
    has-decidable-equality-ℕ
    ( has-decidable-equality-coprod
      has-decidable-equality-unit
      has-decidable-equality-ℕ)

is-decidable-is-zero-ℤ :
  (x : ℤ) → is-decidable (is-zero-ℤ x)
is-decidable-is-zero-ℤ x = has-decidable-equality-ℤ x zero-ℤ

is-decidable-is-one-ℤ :
  (x : ℤ) → is-decidable (is-one-ℤ x)
is-decidable-is-one-ℤ x = has-decidable-equality-ℤ x one-ℤ

is-decidable-is-neg-one-ℤ :
  (x : ℤ) → is-decidable (is-neg-one-ℤ x)
is-decidable-is-neg-one-ℤ x = has-decidable-equality-ℤ x neg-one-ℤ
```

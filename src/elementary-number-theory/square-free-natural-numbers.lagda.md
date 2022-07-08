---
title: Square-free natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.square-free-natural-numbers where

open import elementary-number-theory.divisibility-natural-numbers using (div-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; is-one-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( square-ℕ)

open import foundation.universe-levels using (UU; lzero)
```

## Idea

A natural number `n` is said to be square-free if `x² | n ⇒ x = 1` for any natural number `x`.

## Definition

```agda
is-square-free-ℕ : ℕ → UU lzero
is-square-free-ℕ n = (x : ℕ) → div-ℕ (square-ℕ x) n → is-one-ℕ x
```

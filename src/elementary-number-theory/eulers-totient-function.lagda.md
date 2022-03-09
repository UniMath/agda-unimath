# Euler's totient function

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module elementary-number-theory.eulers-totient-function where

open import elementary-number-theory
open import foundation
open import univalent-combinatorics
```

## Idea

Euler's totient function `φ : ℕ → ℕ` is the function that maps a natural number `n` to the number of `x < n` that are relatively prime with `n`.

## Definition


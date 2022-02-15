# Falling factorials

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.falling-factorials where

open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
```

## Idea

The falling factorial (n)_m is the number n(n-1)⋯(n-m+1)

## Definition

```agda
falling-factorial-ℕ : ℕ → ℕ → ℕ
falling-factorial-ℕ zero-ℕ zero-ℕ = 1
falling-factorial-ℕ zero-ℕ (succ-ℕ m) = 0
falling-factorial-ℕ (succ-ℕ n) zero-ℕ = 1
falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) =
  mul-ℕ (succ-ℕ n) (falling-factorial-ℕ n m)
```

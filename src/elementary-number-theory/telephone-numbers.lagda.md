# Telephone numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.telephone-numbers where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using (mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.universe-levels using (UU; lzero)

open import univalent-combinatorics.standard-finite-types using (nat-Fin; strict-upper-bound-nat-Fin)
```

## Idea

The Catalan numbers are a sequence of natural numbers that count the way `n` telephone lines can be connected to each other, where each line can be connected to at most one other line. They also occur in several other combinatorics problems.

## Definitions

```agda
telephone-numbers : ℕ → ℕ
telephone-numbers zero-ℕ = succ-ℕ zero-ℕ
telephone-numbers (succ-ℕ zero-ℕ) = succ-ℕ zero-ℕ
telephone-numbers (succ-ℕ (succ-ℕ n)) =
  add-ℕ (telephone-numbers (succ-ℕ n)) (mul-ℕ (succ-ℕ n) (telephone-numbers n))
```

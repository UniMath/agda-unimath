---
title: Integer partitions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.integer-partitions where

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.lists
```

## Idea

An integer partition of a natural number n is a list of nonzero natural numbers that sum up to n.

## Definition

```agda
list-nonzero-ℕ : UU lzero
list-nonzero-ℕ = list nonzero-ℕ

sum-list-nonzero-ℕ : list-nonzero-ℕ → ℕ
sum-list-nonzero-ℕ nil = 0
sum-list-nonzero-ℕ (cons x l) = add-ℕ (nat-nonzero-ℕ x) (sum-list-nonzero-ℕ l)

integer-partition' : ℕ → UU lzero
integer-partition' = fib sum-list-nonzero-ℕ

integer-partition : ℕ → UU (lsuc lzero)
integer-partition n =
  Σ 𝔽 (λ X → Σ (type-𝔽 X → nonzero-ℕ) (λ f → Id {!!} {!!}))
```

---
title: Counting the elements of the fiber of a map
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-fibers-of-maps where

open import elementary-number-theory.sums-of-natural-numbers using
  ( sum-count-ℕ)

open import foundation.fibers-of-maps using (fib; equiv-total-fib)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; count-equiv'; number-of-elements-count)
open import univalent-combinatorics.counting-dependent-pair-types using
  ( count-fiber-count-Σ; sum-number-of-elements-count-fiber-count-Σ)
open import univalent-combinatorics.double-counting using (double-counting)
```

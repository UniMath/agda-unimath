---
title: Decidable dependent function types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.decidable-dependent-function-types where

open import foundation.decidable-dependent-function-types public

open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; leq-zero-ℕ; contradiction-leq-ℕ; is-decidable-leq-ℕ; leq-le-ℕ; le-ℕ;
    is-decidable-le-ℕ)
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers using
  ( is-upper-bound-ℕ; is-strict-upper-bound-ℕ)

open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.empty-types
open import foundation.functions
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

## Idea

We describe conditions under which dependent products are decidable.

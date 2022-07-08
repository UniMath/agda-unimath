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
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; ind-ℕ)
open import elementary-number-theory.upper-bounds-natural-numbers using
  ( is-upper-bound-ℕ; is-strict-upper-bound-ℕ)

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-fam; is-decidable-function-type)
open import foundation.empty-types using (ind-empty; ex-falso)
open import foundation.functions using (id)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

We describe conditions under which dependent products are decidable.

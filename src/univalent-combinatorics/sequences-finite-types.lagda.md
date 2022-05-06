---
title: Sequences of elements in finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.sequences-finite-types where

open import elementary-number-theory.natural-numbers

open import foundation.repetitions-sequences
open import foundation.sequences

open import univalent-combinatorics.standard-finite-types
```

## Idea

Sequences of elements in finite types must have repetitions. Furthermore, since equality in finite types is decidable, there must be a first repetition in any sequence of elements in a finite type.

## Properties

```agda
repetition-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) → repetition-sequence f
repetition-sequence-Fin = ?
```

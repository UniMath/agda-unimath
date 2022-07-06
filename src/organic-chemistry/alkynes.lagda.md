---
title: Alkynes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module organic-chemistry.alkynes where

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.embeddings

open import univalent-combinatorics.finite-types

open import organic-chemistry.saturated-carbons
open import organic-chemistry.hydrocarbons
```

## Idea

An **n-alkyne** is a hydrocarbon equipped with a choice of $n$ carbons, each of which has a triple bond.

## Definition

```agda
n-alkyne : hydrocarbon → ℕ → UU (lsuc lzero)
n-alkyne H n =
  Σ (UU-Fin n) λ carbons →
    Σ (type-UU-Fin carbons ↪ vertex-hydrocarbon H) λ embed-carbons →
      (c : type-UU-Fin carbons) → has-triple-bond-hydrocarbon H (pr1 embed-carbons c)
```

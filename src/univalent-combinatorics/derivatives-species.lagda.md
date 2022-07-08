---
title: Derivatives of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.derivatives-species where

open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

## Idea

When we think of a species as the coefficients of a formal power series, the derivative of a species is the species representing the derivative of that formal power series.

## Definition

```agda
derivative-species :
  {l : Level} → species l → species l
derivative-species F X = F (coprod-𝔽 X unit-𝔽)
```

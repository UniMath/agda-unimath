---
title: Finite species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.finite-species where

open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

## Definition

```agda
finite-species : UU (lsuc lzero)
finite-species = 𝔽 → 𝔽
```

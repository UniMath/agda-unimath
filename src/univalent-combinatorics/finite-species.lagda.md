---
title: Finite species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.finite-species where

open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

### Idea

In this file, we define the type of finite species. A finite
species is just a map from 𝔽 to 𝔽.

## Definition

```agda
finite-species : UU (lsuc lzero)
finite-species = 𝔽 → 𝔽

species-finite-species : finite-species → species lzero
species-finite-species F X = type-𝔽 X
```

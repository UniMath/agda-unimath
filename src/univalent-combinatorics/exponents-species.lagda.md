---
title: Exponents of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.exponents-species where

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types 
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.species
```

## Idea

The exponent of two species `F` and `G` is the pointwise exponent

## Definition

### Exponents of species

```agda
function-species : {l1 l2 : Level} → species l1 → species l2 → 𝔽 → UU (l1 ⊔ l2)
function-species F G X = F X → G X
```

---
title: Coproducts of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.coproducts-species where

open import foundation.coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.species
```

## Idea

The coproduct of two species `F` and `G` is the pointwise coproduct.

## Definition

### coproduct on objects

```agda
coprod-species :
  {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
coprod-species F G X = coprod (F X) (G X)
```

   

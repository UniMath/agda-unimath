---
title: Cartesian products of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cartesian-products-species where

open import foundation.cartesian-product-types 
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

## Idea

The cartesian product of two species `F` and `G` is their pointwise cartesian product.


## Definition

```agda 
prod-species :
  {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
prod-species F G X = (F X) × (G X)
``` 

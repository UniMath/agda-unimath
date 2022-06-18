---
title: Cartesian products of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.cartesian-products-species where

open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.equivalences-species
open import univalent-combinatorics.exponents-species
```

## Idea

The cartesian product of two species `F` and `G` is their pointwise cartesian product.

## Definition

```agda
prod-species :
  {l1 l2 : Level} (F : species l1) (G : species l2) (X : 𝔽) → UU (l1 ⊔ l2)
prod-species F G X = (F X) × (G X)
```

## Properties

### The adjunction between cartesian products and exponents of species

```agda 
equiv-universal-property-exponents-species :
  {l1 l2 l3 : Level} (F : species l1) (G : species l2) (H : species l3) →
  hom-species (prod-species F G) H ≃ hom-species F (function-species G H)
equiv-universal-property-exponents-species F G H =
  equiv-map-Π (λ X → equiv-ev-pair)
``` 

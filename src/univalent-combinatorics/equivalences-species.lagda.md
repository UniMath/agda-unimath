---
title: Equivalences of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.equivalences-species where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.functions
open import foundation.equivalences
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species

```

## Idea

An equivalence of species from `F` to `G` is a pointwise equivalence.

## Definition

```agda
equiv-species :
  {l1 l2 : Level} → species l1 → species l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
equiv-species F G = (X : 𝔽) → F X ≃ G X
```

## Properties

### The identity type of two species is equivalent to the type of equivalences between them

```agda
extensionality-species :
  {l : Level} → (F G : species l) → (Id F G) ≃ (equiv-species F G)  
extensionality-species = extensionality-fam
```

 

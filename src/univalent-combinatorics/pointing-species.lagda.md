---
title: Pointing of species
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.pointing-species where

open import foundation.cartesian-product-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

## Idea

A pointing of a species `F` is the species `F*` given by `F* X := X × (F X)`. In other words, it is the species of pointed `F`-structures

## Definition

```agda
pointing-species : {l : Level} → species l → species l
pointing-species F X = type-𝔽 X × F X
```

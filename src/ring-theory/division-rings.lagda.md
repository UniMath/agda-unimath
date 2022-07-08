---
title: Division rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.division-rings where

open import foundation.cartesian-product-types using (_×_)
open import foundation.identity-types using (Id)
open import foundation.negation using (¬)
open import foundation.universe-levels using (Level; UU)

open import ring-theory.invertible-elements-rings using
  ( is-invertible-element-Ring)
open import ring-theory.nontrivial-rings using (is-nontrivial-Ring)
open import ring-theory.rings using (Ring; type-Ring; zero-Ring)
```

## Idea

Division rings are nontrivial rings in which all nonzero elements are invertible.

## Definition

```agda
is-division-Ring :
  { l : Level} → Ring l → UU l
is-division-Ring R =
  (is-nontrivial-Ring R) ×
  ((x : type-Ring R) → ¬ (Id (zero-Ring R) x) → is-invertible-element-Ring R x)
```

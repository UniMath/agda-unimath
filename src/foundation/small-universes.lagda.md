---
title: Small universes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.small-universes where

open import foundation.cartesian-product-types
open import foundation.small-types
open import foundation.universe-levels
```

## Idea

A universe `UU l1` is said to be small with respect to `UU l2` if `UU l1` is a `UU l2`-small type and each `X : UU l1` is a `UU l2`-small type

```agda
is-small-universe :
  (l l1 : Level) → UU (lsuc l1 ⊔ lsuc l)
is-small-universe l l1 = is-small l (UU l1) × ((X : UU l1) → is-small l X)
```

---
title: Equality of cartesian product types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equality-cartesian-product-types where

open import foundation-core.equality-cartesian-product-types public

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_; is-equiv-has-inverse)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (_＝_; refl; ap)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

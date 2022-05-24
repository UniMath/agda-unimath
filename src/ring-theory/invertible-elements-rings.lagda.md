---
title: Invertible elements in rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.invertible-elements-rings where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop-type-Prop; is-prop)
open import foundation.universe-levels using (Level; UU)

open import group-theory.invertible-elements-monoids

open import ring-theory.rings using
  ( Ring; type-Ring; one-Ring; mul-Ring; multiplicative-monoid-Ring)
```

## Idea

Invertible elements are elements that have a two-sided multiplicative inverse. Such elements are also called the units of the Ring. The set of units of any ring forms a group.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where
  
  has-left-inverse-Ring : type-Ring R → UU l
  has-left-inverse-Ring x =
    Σ (type-Ring R) (λ y → Id (mul-Ring R y x) (one-Ring R))
  
  has-right-inverse-Ring : type-Ring R → UU l
  has-right-inverse-Ring x =
    Σ (type-Ring R) (λ y → Id (mul-Ring R x y) (one-Ring R))
  
  has-two-sided-inverse-Ring : type-Ring R → UU l
  has-two-sided-inverse-Ring x =
    ( has-left-inverse-Ring x) × (has-right-inverse-Ring x)

  is-invertible-element-ring-Prop : type-Ring R → UU-Prop l
  is-invertible-element-ring-Prop =
    is-invertible-element-monoid-Prop (multiplicative-monoid-Ring R)
    
  is-invertible-element-Ring : type-Ring R → UU l
  is-invertible-element-Ring x =
    type-Prop (is-invertible-element-ring-Prop x)

  is-prop-is-invertible-element-Ring :
    (x : type-Ring R) → is-prop (is-invertible-element-Ring x)
  is-prop-is-invertible-element-Ring x =
    is-prop-type-Prop (is-invertible-element-ring-Prop x)
```

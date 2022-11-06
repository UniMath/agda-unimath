# Interval subposets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.interval-subposets where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using (Prop; prod-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.posets using (Poset; element-Poset; leq-poset-Prop)
open import order-theory.subposets using (sub-Poset)
```

## Idea

Given two elements `x` and `y` in a poset `X`, the interval `[x, y]` is the subposet of `X` consisting of all elements `z` in `X` such that `x ≤ z` and `z ≤ y`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) (x y : element-Poset X)
  where

  is-in-interval-Poset : (z : element-Poset X) → Prop l2
  is-in-interval-Poset z =
    prod-Prop (leq-poset-Prop X x z) (leq-poset-Prop X z y)

  interval-sub-Poset : Poset (l1 ⊔ l2) l2
  interval-sub-Poset = sub-Poset X is-in-interval-Poset
```

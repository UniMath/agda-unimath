# Interval subposets

```agda
module order-theory.interval-subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.subposets
```

</details>

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

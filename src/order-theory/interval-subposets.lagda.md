# Interval subposets

```agda
module order-theory.interval-subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types

open import order-theory.posets
open import order-theory.subposets
```

</details>

## Idea

Given two elements `x` and `y` in a poset `X`, the **interval subposet**
`[x, y]` is the subposet of `X` consisting of all elements `z` in `X` such that
`x ≤ z` and `z ≤ y`. Note that interval subposets need not be linearly ordered.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) (x y : type-Poset X)
  where

  is-in-interval-Poset : (z : type-Poset X) → Prop l2
  is-in-interval-Poset z =
    product-Prop (leq-Poset-Prop X x z) (leq-Poset-Prop X z y)

  poset-interval-Subposet : Poset (l1 ⊔ l2) l2
  poset-interval-Subposet = poset-Subposet X is-in-interval-Poset
```

### The predicate of an interval being inhabited

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) (x y : type-Poset X)
  where

  is-inhabited-interval : UU (l1 ⊔ l2)
  is-inhabited-interval =
    is-inhabited (type-Poset (poset-interval-Subposet X x y))

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where
  
  inhabited-interval : UU (l1 ⊔ l2)
  inhabited-interval =
    Σ (type-Poset X × type-Poset X) (λ (p , q) → is-inhabited-interval)
```

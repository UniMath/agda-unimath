# Locally finite posets

```agda
module order-theory.locally-finite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.finite-posets
open import order-theory.interval-subposets
open import order-theory.posets
```

</details>

## Idea

A poset `X` is said to be locally finite if for every `x, y ∈ X`, the poset `[x, y]` consisting of `z ∈ X` such that `x ≤ z ≤ y`, is finite.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-locally-finite-poset-Prop : Prop (l1 ⊔ l2)
  is-locally-finite-poset-Prop =
    Π-Prop
      ( element-Poset X)
      ( λ x →
        Π-Prop
          ( element-Poset X)
          ( λ y →
            is-finite-poset-Prop (interval-sub-Poset X x y)))

  is-locally-finite-Poset : UU (l1 ⊔ l2)
  is-locally-finite-Poset = type-Prop is-locally-finite-poset-Prop

  is-prop-is-locally-finite-Poset : is-prop is-locally-finite-Poset
  is-prop-is-locally-finite-Poset =
    is-prop-type-Prop is-locally-finite-poset-Prop
```

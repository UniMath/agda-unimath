# Locally finite posets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.locally-finite-posets where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop-type-Prop; is-prop; Π-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.posets using (Poset; element-Poset; leq-Poset)

open import univalent-combinatorics.finite-types using (is-finite-Prop)
```

## Idea

A poset `X` is said to be locally finite if for every `x, y ∈ X`, the poset `[x, y]` consisting of `z ∈ X` such that `x ≤ z ≤ y`, is finite.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where
  
  is-locally-finite-poset-Prop : UU-Prop (l1 ⊔ l2)
  is-locally-finite-poset-Prop =
    Π-Prop
      ( element-Poset X)
      ( λ x →
        Π-Prop
          ( element-Poset X)
          ( λ y →
            is-finite-Prop
              ( Σ (element-Poset X) (λ z → leq-Poset X x z × leq-Poset X z y))))

  is-locally-finite-Poset : UU (l1 ⊔ l2)
  is-locally-finite-Poset = type-Prop is-locally-finite-poset-Prop

  is-prop-is-locally-finite-Poset : is-prop is-locally-finite-Poset
  is-prop-is-locally-finite-Poset =
    is-prop-type-Prop is-locally-finite-poset-Prop
```

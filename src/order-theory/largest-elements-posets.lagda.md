# Largest elements in posets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.largest-elements-posets where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( Prop; is-prop; all-elements-equal; is-prop-all-elements-equal)
open import foundation.subtypes using (eq-type-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.largest-elements-preorders using
  ( is-largest-element-preorder-Prop; is-largest-element-Preorder;
    is-prop-is-largest-element-Preorder; largest-element-Preorder)
open import order-theory.posets using
  ( Poset; element-Poset; preorder-Poset; antisymmetric-leq-Poset)
```

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-largest-element-poset-Prop : element-Poset X → Prop (l1 ⊔ l2)
  is-largest-element-poset-Prop =
    is-largest-element-preorder-Prop (preorder-Poset X)

  is-largest-element-Poset : element-Poset X → UU (l1 ⊔ l2)
  is-largest-element-Poset = is-largest-element-Preorder (preorder-Poset X)

  is-prop-is-largest-element-Poset :
    (x : element-Poset X) → is-prop (is-largest-element-Poset x)
  is-prop-is-largest-element-Poset =
    is-prop-is-largest-element-Preorder (preorder-Poset X)

  largest-element-Poset : UU (l1 ⊔ l2)
  largest-element-Poset = largest-element-Preorder (preorder-Poset X)

  all-elements-equal-largest-element-Poset :
    all-elements-equal largest-element-Poset
  all-elements-equal-largest-element-Poset (pair x H) (pair y K) =
    eq-type-subtype
      ( is-largest-element-poset-Prop)
      ( antisymmetric-leq-Poset X x y (K x) (H y))

  is-prop-largest-element-Poset : is-prop largest-element-Poset
  is-prop-largest-element-Poset =
    is-prop-all-elements-equal all-elements-equal-largest-element-Poset

  has-largest-element-poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-largest-element-poset-Prop = largest-element-Poset
  pr2 has-largest-element-poset-Prop = is-prop-largest-element-Poset
```

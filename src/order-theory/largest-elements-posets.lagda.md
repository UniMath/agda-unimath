# Largest elements in posets

```agda
module order-theory.largest-elements-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.largest-elements-preorders
open import order-theory.posets
```

</details>

## Idea

A **largest element** in a poset is an element `t` such that `x ≤ t` holds for
every `x : P`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-largest-element-Poset-Prop : type-Poset X → Prop (l1 ⊔ l2)
  is-largest-element-Poset-Prop =
    is-largest-element-Preorder-Prop (preorder-Poset X)

  is-largest-element-Poset : type-Poset X → UU (l1 ⊔ l2)
  is-largest-element-Poset = is-largest-element-Preorder (preorder-Poset X)

  is-prop-is-largest-element-Poset :
    (x : type-Poset X) → is-prop (is-largest-element-Poset x)
  is-prop-is-largest-element-Poset =
    is-prop-is-largest-element-Preorder (preorder-Poset X)

  largest-element-Poset : UU (l1 ⊔ l2)
  largest-element-Poset = largest-element-Preorder (preorder-Poset X)

  all-elements-equal-largest-element-Poset :
    all-elements-equal largest-element-Poset
  all-elements-equal-largest-element-Poset (pair x H) (pair y K) =
    eq-type-subtype
      ( is-largest-element-Poset-Prop)
      ( antisymmetric-leq-Poset X x y (K x) (H y))

  is-prop-largest-element-Poset : is-prop largest-element-Poset
  is-prop-largest-element-Poset =
    is-prop-all-elements-equal all-elements-equal-largest-element-Poset

  has-largest-element-Poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-largest-element-Poset-Prop = largest-element-Poset
  pr2 has-largest-element-Poset-Prop = is-prop-largest-element-Poset
```

# Top elements in posets

```agda
module order-theory.top-elements-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.top-elements-preorders
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

  is-top-element-Poset-Prop : type-Poset X → Prop (l1 ⊔ l2)
  is-top-element-Poset-Prop =
    is-top-element-Preorder-Prop (preorder-Poset X)

  is-top-element-Poset : type-Poset X → UU (l1 ⊔ l2)
  is-top-element-Poset = is-top-element-Preorder (preorder-Poset X)

  is-prop-is-top-element-Poset :
    (x : type-Poset X) → is-prop (is-top-element-Poset x)
  is-prop-is-top-element-Poset =
    is-prop-is-top-element-Preorder (preorder-Poset X)

  has-top-element-Poset : UU (l1 ⊔ l2)
  has-top-element-Poset = has-top-element-Preorder (preorder-Poset X)

  all-elements-equal-has-top-element-Poset :
    all-elements-equal has-top-element-Poset
  all-elements-equal-has-top-element-Poset (pair x H) (pair y K) =
    eq-type-subtype
      ( is-top-element-Poset-Prop)
      ( antisymmetric-leq-Poset X x y (K x) (H y))

  is-prop-has-top-element-Poset : is-prop has-top-element-Poset
  is-prop-has-top-element-Poset =
    is-prop-all-elements-equal all-elements-equal-has-top-element-Poset

  has-top-element-Poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-top-element-Poset-Prop = has-top-element-Poset
  pr2 has-top-element-Poset-Prop = is-prop-has-top-element-Poset
```

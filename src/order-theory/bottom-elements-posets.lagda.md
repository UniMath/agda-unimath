# Bottom elements in posets

```agda
module order-theory.bottom-elements-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.bottom-elements-preorders
open import order-theory.posets
```

</details>

## Idea

A **bottom element** in a poset `P` is an element `b` such that `b ≤ x` holds
for every element `x : P`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-bottom-element-Poset-Prop : type-Poset X → Prop (l1 ⊔ l2)
  is-bottom-element-Poset-Prop =
    is-bottom-element-Preorder-Prop (preorder-Poset X)

  is-bottom-element-Poset : type-Poset X → UU (l1 ⊔ l2)
  is-bottom-element-Poset = is-bottom-element-Preorder (preorder-Poset X)

  is-prop-is-bottom-element-Poset :
    (x : type-Poset X) → is-prop (is-bottom-element-Poset x)
  is-prop-is-bottom-element-Poset =
    is-prop-is-bottom-element-Preorder (preorder-Poset X)

  has-bottom-element-Poset : UU (l1 ⊔ l2)
  has-bottom-element-Poset = has-bottom-element-Preorder (preorder-Poset X)

  all-elements-equal-has-bottom-element-Poset :
    all-elements-equal has-bottom-element-Poset
  all-elements-equal-has-bottom-element-Poset (pair x H) (pair y K) =
    eq-type-subtype
      ( is-bottom-element-Poset-Prop)
      ( antisymmetric-leq-Poset X x y (H y) (K x))

  is-prop-has-bottom-element-Poset : is-prop has-bottom-element-Poset
  is-prop-has-bottom-element-Poset =
    is-prop-all-elements-equal all-elements-equal-has-bottom-element-Poset

  has-bottom-element-Poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-bottom-element-Poset-Prop = has-bottom-element-Poset
  pr2 has-bottom-element-Poset-Prop = is-prop-has-bottom-element-Poset
```

# Least elements in posets

```agda
module order-theory.least-elements-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.least-elements-preorders
open import order-theory.posets
```

</details>

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-least-element-Poset-Prop : type-Poset X → Prop (l1 ⊔ l2)
  is-least-element-Poset-Prop =
    is-least-element-Preorder-Prop (preorder-Poset X)

  is-least-element-Poset : type-Poset X → UU (l1 ⊔ l2)
  is-least-element-Poset = is-least-element-Preorder (preorder-Poset X)

  is-prop-is-least-element-Poset :
    (x : type-Poset X) → is-prop (is-least-element-Poset x)
  is-prop-is-least-element-Poset =
    is-prop-is-least-element-Preorder (preorder-Poset X)

  least-element-Poset : UU (l1 ⊔ l2)
  least-element-Poset = least-element-Preorder (preorder-Poset X)

  all-elements-equal-least-element-Poset :
    all-elements-equal least-element-Poset
  all-elements-equal-least-element-Poset (pair x H) (pair y K) =
    eq-type-subtype
      ( is-least-element-Poset-Prop)
      ( antisymmetric-leq-Poset X x y (H y) (K x))

  is-prop-least-element-Poset : is-prop least-element-Poset
  is-prop-least-element-Poset =
    is-prop-all-elements-equal all-elements-equal-least-element-Poset

  has-least-element-Poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-least-element-Poset-Prop = least-element-Poset
  pr2 has-least-element-Poset-Prop = is-prop-least-element-Poset
```

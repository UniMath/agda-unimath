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

# Bottom elements in preorders

```agda
module order-theory.bottom-elements-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **bottom element** in a preorder `P` is an element `b` such that `b ≤ x` holds
for every element `x : P`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-bottom-element-Preorder-Prop : type-Preorder X → Prop (l1 ⊔ l2)
  is-bottom-element-Preorder-Prop x =
    Π-Prop (type-Preorder X) (leq-prop-Preorder X x)

  is-bottom-element-Preorder : type-Preorder X → UU (l1 ⊔ l2)
  is-bottom-element-Preorder x = type-Prop (is-bottom-element-Preorder-Prop x)

  is-prop-is-bottom-element-Preorder :
    (x : type-Preorder X) → is-prop (is-bottom-element-Preorder x)
  is-prop-is-bottom-element-Preorder x =
    is-prop-type-Prop (is-bottom-element-Preorder-Prop x)

  has-bottom-element-Preorder : UU (l1 ⊔ l2)
  has-bottom-element-Preorder = Σ (type-Preorder X) is-bottom-element-Preorder
```

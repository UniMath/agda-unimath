# Least elements in preorders

```agda
module order-theory.least-elements-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **least element** in a preorder `P` is an element `b` such that `b ≤ x` holds
for every element `x : P`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-least-element-Preorder-Prop : type-Preorder X → Prop (l1 ⊔ l2)
  is-least-element-Preorder-Prop x =
    Π-Prop (type-Preorder X) (leq-Preorder-Prop X x)

  is-least-element-Preorder : type-Preorder X → UU (l1 ⊔ l2)
  is-least-element-Preorder x = type-Prop (is-least-element-Preorder-Prop x)

  is-prop-is-least-element-Preorder :
    (x : type-Preorder X) → is-prop (is-least-element-Preorder x)
  is-prop-is-least-element-Preorder x =
    is-prop-type-Prop (is-least-element-Preorder-Prop x)

  least-element-Preorder : UU (l1 ⊔ l2)
  least-element-Preorder = Σ (type-Preorder X) is-least-element-Preorder
```

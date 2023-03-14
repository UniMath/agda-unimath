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

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-least-element-preorder-Prop : element-Preorder X → Prop (l1 ⊔ l2)
  is-least-element-preorder-Prop x =
    Π-Prop (element-Preorder X) (leq-preorder-Prop X x)

  is-least-element-Preorder : element-Preorder X → UU (l1 ⊔ l2)
  is-least-element-Preorder x = type-Prop (is-least-element-preorder-Prop x)

  is-prop-is-least-element-Preorder :
    (x : element-Preorder X) → is-prop (is-least-element-Preorder x)
  is-prop-is-least-element-Preorder x =
    is-prop-type-Prop (is-least-element-preorder-Prop x)

  least-element-Preorder : UU (l1 ⊔ l2)
  least-element-Preorder = Σ (element-Preorder X) is-least-element-Preorder
```

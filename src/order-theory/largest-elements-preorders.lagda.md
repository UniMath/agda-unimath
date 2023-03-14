# Largest elements in preorders

```agda
module order-theory.largest-elements-preorders where

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

## Definition

```
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-largest-element-preorder-Prop : element-Preorder X → Prop (l1 ⊔ l2)
  is-largest-element-preorder-Prop x =
    Π-Prop (element-Preorder X) (λ y → leq-preorder-Prop X y x)

  is-largest-element-Preorder : element-Preorder X → UU (l1 ⊔ l2)
  is-largest-element-Preorder x = type-Prop (is-largest-element-preorder-Prop x)

  is-prop-is-largest-element-Preorder :
    (x : element-Preorder X) → is-prop (is-largest-element-Preorder x)
  is-prop-is-largest-element-Preorder x =
    is-prop-type-Prop (is-largest-element-preorder-Prop x)

  largest-element-Preorder : UU (l1 ⊔ l2)
  largest-element-Preorder = Σ (element-Preorder X) is-largest-element-Preorder
```

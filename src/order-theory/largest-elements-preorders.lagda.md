# Largest elements in preorders

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.largest-elements-preorders where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( UU-Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.preorders using
  ( Preorder; element-Preorder; leq-preorder-Prop)
```

## Definition

```
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-largest-element-preorder-Prop : element-Preorder X → UU-Prop (l1 ⊔ l2)
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


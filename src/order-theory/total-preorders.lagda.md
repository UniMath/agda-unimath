# Total preorders

```agda
module order-theory.total-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.disjunction
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

  incident-preorder-Prop : (x y : element-Preorder X) → Prop l2
  incident-preorder-Prop x y =
    disj-Prop (leq-preorder-Prop X x y) (leq-preorder-Prop X y x)

  incident-Preorder : (x y : element-Preorder X) → UU l2
  incident-Preorder x y = type-Prop (incident-preorder-Prop x y)

  is-prop-incident-Preorder :
    (x y : element-Preorder X) → is-prop (incident-Preorder x y)
  is-prop-incident-Preorder x y = is-prop-type-Prop (incident-preorder-Prop x y)

  is-total-preorder-Prop : Prop (l1 ⊔ l2)
  is-total-preorder-Prop =
    Π-Prop
      ( element-Preorder X)
      ( λ x → Π-Prop ( element-Preorder X) (λ y → incident-preorder-Prop x y))

  is-total-Preorder : UU (l1 ⊔ l2)
  is-total-Preorder = type-Prop is-total-preorder-Prop

  is-prop-is-total-Preorder : is-prop is-total-Preorder
  is-prop-is-total-Preorder = is-prop-type-Prop is-total-preorder-Prop
```

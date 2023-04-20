# Total preorders

```agda
module order-theory.total-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Definition

### Being a total preorder

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

### The type of total preorder

```agda
total-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
total-Preorder l1 l2 = Σ (Preorder l1 l2) is-total-Preorder

module _
  {l1 l2 : Level} (X : total-Preorder l1 l2)
  where

  Preorder-total-Preorder : Preorder l1 l2
  Preorder-total-Preorder = pr1 X

  is-total-Preorder-total-Preorder : is-total-Preorder Preorder-total-Preorder
  is-total-Preorder-total-Preorder = pr2 X

  element-total-Preorder : UU l1
  element-total-Preorder = pr1 Preorder-total-Preorder

  leq-total-preorder-Prop : (x y : element-total-Preorder) → Prop l2
  leq-total-preorder-Prop = pr1 (pr2 Preorder-total-Preorder)

  leq-total-Preorder : (x y : element-total-Preorder) → UU l2
  leq-total-Preorder x y = type-Prop (leq-total-preorder-Prop x y)

  is-prop-leq-total-Preorder : (x y : element-total-Preorder) → is-prop (leq-total-Preorder x y)
  is-prop-leq-total-Preorder x y = is-prop-type-Prop (leq-total-preorder-Prop x y)

  refl-leq-total-Preorder : (x : element-total-Preorder) → leq-total-Preorder x x
  refl-leq-total-Preorder = pr1 (pr2 (pr2 Preorder-total-Preorder))

  transitive-leq-total-Preorder :
    (x y z : element-total-Preorder) →
    leq-total-Preorder y z → leq-total-Preorder x y → leq-total-Preorder x z
  transitive-leq-total-Preorder = pr2 (pr2 (pr2 Preorder-total-Preorder))
```

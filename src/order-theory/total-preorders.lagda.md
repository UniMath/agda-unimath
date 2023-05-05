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

  incident-Preorder-Prop : (x y : element-Preorder X) → Prop l2
  incident-Preorder-Prop x y =
    disj-Prop (leq-Preorder-Prop X x y) (leq-Preorder-Prop X y x)

  incident-Preorder : (x y : element-Preorder X) → UU l2
  incident-Preorder x y = type-Prop (incident-Preorder-Prop x y)

  is-prop-incident-Preorder :
    (x y : element-Preorder X) → is-prop (incident-Preorder x y)
  is-prop-incident-Preorder x y = is-prop-type-Prop (incident-Preorder-Prop x y)

  is-total-Preorder-Prop : Prop (l1 ⊔ l2)
  is-total-Preorder-Prop =
    Π-Prop
      ( element-Preorder X)
      ( λ x → Π-Prop ( element-Preorder X) (λ y → incident-Preorder-Prop x y))

  is-total-Preorder : UU (l1 ⊔ l2)
  is-total-Preorder = type-Prop is-total-Preorder-Prop

  is-prop-is-total-Preorder : is-prop is-total-Preorder
  is-prop-is-total-Preorder = is-prop-type-Prop is-total-Preorder-Prop
```

### The type of total preorder

```agda
Total-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Total-Preorder l1 l2 = Σ (Preorder l1 l2) is-total-Preorder

module _
  {l1 l2 : Level} (X : Total-Preorder l1 l2)
  where

  preorder-Total-Preorder : Preorder l1 l2
  preorder-Total-Preorder = pr1 X

  is-total-preorder-Total-Preorder : is-total-Preorder preorder-Total-Preorder
  is-total-preorder-Total-Preorder = pr2 X

  element-Total-Preorder : UU l1
  element-Total-Preorder = element-Preorder preorder-Total-Preorder

  leq-Total-Preorder-Prop : (x y : element-Total-Preorder) → Prop l2
  leq-Total-Preorder-Prop = leq-Preorder-Prop preorder-Total-Preorder

  leq-Total-Preorder : (x y : element-Total-Preorder) → UU l2
  leq-Total-Preorder = leq-Preorder preorder-Total-Preorder

  is-prop-leq-Total-Preorder :
    (x y : element-Total-Preorder) → is-prop (leq-Total-Preorder x y)
  is-prop-leq-Total-Preorder = is-prop-leq-Preorder preorder-Total-Preorder

  refl-leq-Total-Preorder :
    (x : element-Total-Preorder) → leq-Total-Preorder x x
  refl-leq-Total-Preorder = refl-leq-Preorder preorder-Total-Preorder

  transitive-leq-Total-Preorder :
    (x y z : element-Total-Preorder) →
    leq-Total-Preorder y z → leq-Total-Preorder x y → leq-Total-Preorder x z
  transitive-leq-Total-Preorder =
    transitive-leq-Preorder preorder-Total-Preorder
```

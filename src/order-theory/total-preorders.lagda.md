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
total-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
total-Preorder l1 l2 = Σ (Preorder l1 l2) is-total-Preorder

module _
  {l1 l2 : Level} (X : total-Preorder l1 l2)
  where

  preorder-total-Preorder : Preorder l1 l2
  preorder-total-Preorder = pr1 X

  is-total-preorder-total-Preorder : is-total-Preorder preorder-total-Preorder
  is-total-preorder-total-Preorder = pr2 X

  element-total-Preorder : UU l1
  element-total-Preorder = element-Preorder preorder-total-Preorder

  leq-total-Preorder-Prop : (x y : element-total-Preorder) → Prop l2
  leq-total-Preorder-Prop = leq-Preorder-Prop preorder-total-Preorder

  leq-total-Preorder : (x y : element-total-Preorder) → UU l2
  leq-total-Preorder = leq-Preorder preorder-total-Preorder

  is-prop-leq-total-Preorder :
    (x y : element-total-Preorder) → is-prop (leq-total-Preorder x y)
  is-prop-leq-total-Preorder = is-prop-leq-Preorder preorder-total-Preorder

  refl-leq-total-Preorder :
    (x : element-total-Preorder) → leq-total-Preorder x x
  refl-leq-total-Preorder = refl-leq-Preorder preorder-total-Preorder

  transitive-leq-total-Preorder :
    (x y z : element-total-Preorder) →
    leq-total-Preorder y z → leq-total-Preorder x y → leq-total-Preorder x z
  transitive-leq-total-Preorder =
    transitive-leq-Preorder preorder-total-Preorder
```

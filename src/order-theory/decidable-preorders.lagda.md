# Decidable preorders

```agda
module order-theory.decidable-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
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

  is-decidable-leq-Preorder-Prop : Prop (l1 ⊔ l2)
  is-decidable-leq-Preorder-Prop =
    Π-Prop
      ( element-Preorder X)
      ( λ x →
        Π-Prop
          ( element-Preorder X)
          ( λ y → is-decidable-Prop (leq-Preorder-Prop X x y)))

  is-decidable-leq-Preorder : UU (l1 ⊔ l2)
  is-decidable-leq-Preorder = type-Prop is-decidable-leq-Preorder-Prop

  is-prop-is-decidable-leq-Preorder : is-prop is-decidable-leq-Preorder
  is-prop-is-decidable-leq-Preorder =
    is-prop-type-Prop is-decidable-leq-Preorder-Prop

Decidable-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Preorder l1 l2 = Σ (Preorder l1 l2) is-decidable-leq-Preorder

module _
  {l1 l2 : Level} (X : Decidable-Preorder l1 l2)
  where

  preorder-Decidable-Preorder : Preorder l1 l2
  preorder-Decidable-Preorder = pr1 X

  is-decidable-leq-Decidable-Preorder :
    is-decidable-leq-Preorder preorder-Decidable-Preorder
  is-decidable-leq-Decidable-Preorder = pr2 X

  element-Decidable-Preorder : UU l1
  element-Decidable-Preorder = element-Preorder preorder-Decidable-Preorder

  leq-Decidable-Preorder-Prop :
    (x y : element-Decidable-Preorder) → Prop l2
  leq-Decidable-Preorder-Prop =
    leq-Preorder-Prop preorder-Decidable-Preorder

  leq-Decidable-Preorder :
    (x y : element-Decidable-Preorder) → UU l2
  leq-Decidable-Preorder = leq-Preorder preorder-Decidable-Preorder

  is-prop-leq-Decidable-Preorder :
    (x y : element-Decidable-Preorder) →
    is-prop (leq-Decidable-Preorder x y)
  is-prop-leq-Decidable-Preorder =
    is-prop-leq-Preorder preorder-Decidable-Preorder

  leq-Decidable-Preorder-Decidable-Prop :
    (x y : element-Decidable-Preorder) → Decidable-Prop l2
  pr1 (leq-Decidable-Preorder-Decidable-Prop x y) =
    leq-Decidable-Preorder x y
  pr1 (pr2 (leq-Decidable-Preorder-Decidable-Prop x y)) =
    is-prop-leq-Decidable-Preorder x y
  pr2 (pr2 (leq-Decidable-Preorder-Decidable-Prop x y)) =
    is-decidable-leq-Decidable-Preorder x y

  refl-leq-Decidable-Preorder :
    (x : element-Decidable-Preorder) → leq-Decidable-Preorder x x
  refl-leq-Decidable-Preorder = refl-leq-Preorder preorder-Decidable-Preorder

  transitive-leq-Decidable-Preorder :
    (x y z : element-Decidable-Preorder) →
    leq-Decidable-Preorder y z →
    leq-Decidable-Preorder x y →
    leq-Decidable-Preorder x z
  transitive-leq-Decidable-Preorder =
    transitive-leq-Preorder preorder-Decidable-Preorder
```

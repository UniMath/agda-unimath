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

  is-decidable-Preorder-Prop : Prop (l1 ⊔ l2)
  is-decidable-Preorder-Prop =
    Π-Prop
      ( element-Preorder X)
      ( λ x →
        Π-Prop
          ( element-Preorder X)
          ( λ y → is-decidable-Prop (leq-Preorder-Prop X x y)))

  is-decidable-Preorder : UU (l1 ⊔ l2)
  is-decidable-Preorder = type-Prop is-decidable-Preorder-Prop

  is-prop-is-decidable-Preorder : is-prop is-decidable-Preorder
  is-prop-is-decidable-Preorder = is-prop-type-Prop is-decidable-Preorder-Prop

decidable-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
decidable-Preorder l1 l2 = Σ (Preorder l1 l2) is-decidable-Preorder

module _
  {l1 l2 : Level} (X : decidable-Preorder l1 l2)
  where

  preorder-decidable-Preorder : Preorder l1 l2
  preorder-decidable-Preorder = pr1 X

  is-decidable-preorder-decidable-Preorder :
    is-decidable-Preorder preorder-decidable-Preorder
  is-decidable-preorder-decidable-Preorder = pr2 X

  element-decidable-Preorder : UU l1
  element-decidable-Preorder = element-Preorder preorder-decidable-Preorder

  leq-decidable-Preorder-Prop :
    (x y : element-decidable-Preorder) → Prop l2
  leq-decidable-Preorder-Prop =
    leq-Preorder-Prop preorder-decidable-Preorder

  leq-decidable-Preorder :
    (x y : element-decidable-Preorder) → UU l2
  leq-decidable-Preorder = leq-Preorder preorder-decidable-Preorder

  is-prop-leq-decidable-Preorder :
    (x y : element-decidable-Preorder) →
    is-prop (leq-decidable-Preorder x y)
  is-prop-leq-decidable-Preorder =
    is-prop-leq-Preorder preorder-decidable-Preorder

  leq-decidable-preorder-decidable-Prop :
    (x y : element-decidable-Preorder) → Decidable-Prop l2
  pr1 (leq-decidable-preorder-decidable-Prop x y) =
    leq-decidable-Preorder x y
  pr1 (pr2 (leq-decidable-preorder-decidable-Prop x y)) =
    is-prop-leq-decidable-Preorder x y
  pr2 (pr2 (leq-decidable-preorder-decidable-Prop x y)) =
    is-decidable-preorder-decidable-Preorder x y

  refl-leq-decidable-Preorder :
    (x : element-decidable-Preorder) → leq-decidable-Preorder x x
  refl-leq-decidable-Preorder = refl-leq-Preorder preorder-decidable-Preorder

  transitive-leq-decidable-Preorder :
    (x y z : element-decidable-Preorder) →
    leq-decidable-Preorder y z →
    leq-decidable-Preorder x y →
    leq-decidable-Preorder x z
  transitive-leq-decidable-Preorder =
    transitive-leq-Preorder preorder-decidable-Preorder
```

# Decidable preorders

```agda
module order-theory.decidable-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **decidable preorder** is a preorder of which the ordering relation is
decidable.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-decidable-leq-prop-Preorder : Prop (l1 ⊔ l2)
  is-decidable-leq-prop-Preorder =
    Π-Prop
      ( type-Preorder X)
      ( λ x →
        Π-Prop
          ( type-Preorder X)
          ( λ y → is-decidable-Prop (leq-prop-Preorder X x y)))

  is-decidable-leq-Preorder : UU (l1 ⊔ l2)
  is-decidable-leq-Preorder = type-Prop is-decidable-leq-prop-Preorder

  is-prop-is-decidable-leq-Preorder : is-prop is-decidable-leq-Preorder
  is-prop-is-decidable-leq-Preorder =
    is-prop-type-Prop is-decidable-leq-prop-Preorder

Decidable-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Preorder l1 l2 = Σ (Preorder l1 l2) is-decidable-leq-Preorder

module _
  {l1 l2 : Level} (X : Decidable-Preorder l1 l2)
  where

  preorder-Decidable-Preorder : Preorder l1 l2
  preorder-Decidable-Preorder = pr1 X

  is-decidable-leq-Decidable-Preorder :
    is-decidable-leq-Preorder preorder-Decidable-Preorder
  is-decidable-leq-Decidable-Preorder = pr2 X

  type-Decidable-Preorder : UU l1
  type-Decidable-Preorder = type-Preorder preorder-Decidable-Preorder

  leq-Decidable-Preorder-Prop :
    (x y : type-Decidable-Preorder) → Prop l2
  leq-Decidable-Preorder-Prop =
    leq-prop-Preorder preorder-Decidable-Preorder

  leq-Decidable-Preorder :
    (x y : type-Decidable-Preorder) → UU l2
  leq-Decidable-Preorder = leq-Preorder preorder-Decidable-Preorder

  is-prop-leq-Decidable-Preorder :
    (x y : type-Decidable-Preorder) →
    is-prop (leq-Decidable-Preorder x y)
  is-prop-leq-Decidable-Preorder =
    is-prop-leq-Preorder preorder-Decidable-Preorder

  leq-Decidable-Preorder-Decidable-Prop :
    (x y : type-Decidable-Preorder) → Decidable-Prop l2
  pr1 (leq-Decidable-Preorder-Decidable-Prop x y) =
    leq-Decidable-Preorder x y
  pr1 (pr2 (leq-Decidable-Preorder-Decidable-Prop x y)) =
    is-prop-leq-Decidable-Preorder x y
  pr2 (pr2 (leq-Decidable-Preorder-Decidable-Prop x y)) =
    is-decidable-leq-Decidable-Preorder x y

  refl-leq-Decidable-Preorder : is-reflexive leq-Decidable-Preorder
  refl-leq-Decidable-Preorder = refl-leq-Preorder preorder-Decidable-Preorder

  transitive-leq-Decidable-Preorder : is-transitive leq-Decidable-Preorder
  transitive-leq-Decidable-Preorder =
    transitive-leq-Preorder preorder-Decidable-Preorder
```

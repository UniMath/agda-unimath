# Decidable total preorders

```agda
module order-theory.decidable-total-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.decidable-preorders
open import order-theory.preorders
open import order-theory.total-preorders
```

</details>

## Idea

A **decidable total preorder** is a total preorder of which the inequality
relation is decidable.

## Definitions

```agda
Decidable-Total-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Total-Preorder l1 l2 =
  Σ (Preorder l1 l2) (λ X → is-total-Preorder X × is-decidable-leq-Preorder X)

module _
  {l1 l2 : Level} (X : Decidable-Total-Preorder l1 l2)
  where

  preorder-Decidable-Total-Preorder : Preorder l1 l2
  preorder-Decidable-Total-Preorder = pr1 X

  is-total-Decidable-Total-Preorder :
    is-total-Preorder preorder-Decidable-Total-Preorder
  is-total-Decidable-Total-Preorder = pr1 (pr2 X)

  is-decidable-leq-Decidable-Total-Preorder :
    is-decidable-leq-Preorder preorder-Decidable-Total-Preorder
  is-decidable-leq-Decidable-Total-Preorder = pr2 (pr2 X)

  decidable-preorder-Decidable-Total-Preorder : Decidable-Preorder l1 l2
  pr1 decidable-preorder-Decidable-Total-Preorder =
    preorder-Decidable-Total-Preorder
  pr2 decidable-preorder-Decidable-Total-Preorder =
    is-decidable-leq-Decidable-Total-Preorder

  type-Decidable-Total-Preorder : UU l1
  type-Decidable-Total-Preorder =
    type-Preorder preorder-Decidable-Total-Preorder

  leq-Decidable-Total-Preorder-Prop :
    (x y : type-Decidable-Total-Preorder) → Prop l2
  leq-Decidable-Total-Preorder-Prop =
    leq-Preorder-Prop preorder-Decidable-Total-Preorder

  leq-Decidable-Total-Preorder :
    (x y : type-Decidable-Total-Preorder) → UU l2
  leq-Decidable-Total-Preorder =
    leq-Preorder preorder-Decidable-Total-Preorder

  is-prop-leq-Decidable-Total-Preorder :
    (x y : type-Decidable-Total-Preorder) →
    is-prop (leq-Decidable-Total-Preorder x y)
  is-prop-leq-Decidable-Total-Preorder =
    is-prop-leq-Preorder preorder-Decidable-Total-Preorder

  le-Decidable-Total-Preorder-Prop :
    (x y : type-Decidable-Total-Preorder) → Prop (l1 ⊔ l2)
  le-Decidable-Total-Preorder-Prop =
    le-Preorder-Prop preorder-Decidable-Total-Preorder

  le-Decidable-Total-Preorder :
    (x y : type-Decidable-Total-Preorder) → UU (l1 ⊔ l2)
  le-Decidable-Total-Preorder =
    le-Preorder preorder-Decidable-Total-Preorder

  is-prop-le-Decidable-Total-Preorder :
    (x y : type-Decidable-Total-Preorder) →
    is-prop (le-Decidable-Total-Preorder x y)
  is-prop-le-Decidable-Total-Preorder =
    is-prop-le-Preorder preorder-Decidable-Total-Preorder

  leq-Total-Decidable-Preorder-Decidable-Prop :
    (x y : type-Decidable-Total-Preorder) → Decidable-Prop l2
  leq-Total-Decidable-Preorder-Decidable-Prop =
    leq-Decidable-Preorder-Decidable-Prop
      decidable-preorder-Decidable-Total-Preorder

  refl-leq-Decidable-Total-Preorder :
    is-reflexive leq-Decidable-Total-Preorder
  refl-leq-Decidable-Total-Preorder =
    refl-leq-Preorder preorder-Decidable-Total-Preorder

  transitive-leq-Decidable-Total-Preorder :
    is-transitive leq-Decidable-Total-Preorder
  transitive-leq-Decidable-Total-Preorder =
    transitive-leq-Preorder preorder-Decidable-Total-Preorder

  leq-or-strict-greater-Decidable-Preorder :
    (x y : type-Decidable-Total-Preorder) → UU (l1 ⊔ l2)
  leq-or-strict-greater-Decidable-Preorder x y =
    leq-Decidable-Total-Preorder x y + le-Decidable-Total-Preorder y x

  abstract
    helper-is-leq-or-strict-greater-Decidable-Total-Preorder :
      (x y : type-Decidable-Total-Preorder) →
      is-decidable (leq-Decidable-Total-Preorder x y) →
      leq-or-strict-greater-Decidable-Preorder x y
    helper-is-leq-or-strict-greater-Decidable-Total-Preorder x y (inl p) =
      inl p
    helper-is-leq-or-strict-greater-Decidable-Total-Preorder x y (inr p) =
      inr
        ( ( λ where refl → p (refl-leq-Decidable-Total-Preorder x)) ,
          ( apply-universal-property-trunc-Prop
            ( is-total-Decidable-Total-Preorder y x)
            ( leq-Decidable-Total-Preorder-Prop y x)
            ( ind-coproduct
                ( λ _ → leq-Decidable-Total-Preorder y x)
                ( id)
                ( ex-falso ∘ p))))

  is-leq-or-strict-greater-Decidable-Total-Preorder :
    (x y : type-Decidable-Total-Preorder) →
    leq-or-strict-greater-Decidable-Preorder x y
  is-leq-or-strict-greater-Decidable-Total-Preorder x y =
    helper-is-leq-or-strict-greater-Decidable-Total-Preorder
      ( x)
      ( y)
      ( is-decidable-leq-Decidable-Total-Preorder x y)
```

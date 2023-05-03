# Totally ordered decidable preorders

```agda
module order-theory.total-decidable-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functions
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-preorders
open import order-theory.preorders
open import order-theory.total-preorders
```

</details>

## Definitions

```agda
total-decidable-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
total-decidable-Preorder l1 l2 =
  Σ (Preorder l1 l2) (λ X → is-total-Preorder X × is-decidable-Preorder X)

module _
  {l1 l2 : Level} (X : total-decidable-Preorder l1 l2)
  where

  preorder-total-decidable-Preorder : Preorder l1 l2
  preorder-total-decidable-Preorder = pr1 X

  is-total-preorder-total-decidable-Preorder :
    is-total-Preorder preorder-total-decidable-Preorder
  is-total-preorder-total-decidable-Preorder = pr1 (pr2 X)

  is-decidable-preorder-total-decidable-Preorder :
    is-decidable-Preorder preorder-total-decidable-Preorder
  is-decidable-preorder-total-decidable-Preorder = pr2 (pr2 X)

  decidable-preorder-total-decidable-Preorder : decidable-Preorder l1 l2
  pr1 decidable-preorder-total-decidable-Preorder =
    preorder-total-decidable-Preorder
  pr2 decidable-preorder-total-decidable-Preorder =
    is-decidable-preorder-total-decidable-Preorder

  element-total-decidable-Preorder : UU l1
  element-total-decidable-Preorder =
    element-Preorder preorder-total-decidable-Preorder

  leq-total-decidable-preorder-Prop :
    (x y : element-total-decidable-Preorder) → Prop l2
  leq-total-decidable-preorder-Prop =
    leq-preorder-Prop preorder-total-decidable-Preorder

  leq-total-decidable-Preorder :
    (x y : element-total-decidable-Preorder) → UU l2
  leq-total-decidable-Preorder =
    leq-Preorder preorder-total-decidable-Preorder

  is-prop-leq-total-decidable-Preorder :
    (x y : element-total-decidable-Preorder) →
    is-prop (leq-total-decidable-Preorder x y)
  is-prop-leq-total-decidable-Preorder =
    is-prop-leq-Preorder preorder-total-decidable-Preorder

  strict-leq-total-decidable-preorder-Prop :
    (x y : element-total-decidable-Preorder) → Prop (l1 ⊔ l2)
  strict-leq-total-decidable-preorder-Prop =
    strict-leq-preorder-Prop preorder-total-decidable-Preorder

  strict-leq-total-decidable-Preorder :
    (x y : element-total-decidable-Preorder) → UU (l1 ⊔ l2)
  strict-leq-total-decidable-Preorder =
    strict-leq-Preorder preorder-total-decidable-Preorder

  is-prop-strict-leq-total-decidable-Preorder :
    (x y : element-total-decidable-Preorder) →
    is-prop (strict-leq-total-decidable-Preorder x y)
  is-prop-strict-leq-total-decidable-Preorder =
    is-prop-strict-leq-Preorder preorder-total-decidable-Preorder

  is-decidable-leq-total-decidable-Preorder :
    (x y : element-total-decidable-Preorder) →
    is-decidable (leq-total-decidable-Preorder x y)
  is-decidable-leq-total-decidable-Preorder =
    is-decidable-preorder-total-decidable-Preorder

  leq-total-decidable-preorder-decidable-Prop :
    (x y : element-total-decidable-Preorder) → Decidable-Prop l2
  leq-total-decidable-preorder-decidable-Prop =
    leq-decidable-preorder-decidable-Prop
      decidable-preorder-total-decidable-Preorder

  refl-leq-total-decidable-Preorder :
    (x : element-total-decidable-Preorder) → leq-total-decidable-Preorder x x
  refl-leq-total-decidable-Preorder =
    refl-leq-Preorder preorder-total-decidable-Preorder

  transitive-leq-total-decidable-Preorder :
    (x y z : element-total-decidable-Preorder) →
    leq-total-decidable-Preorder y z →
    leq-total-decidable-Preorder x y →
    leq-total-decidable-Preorder x z
  transitive-leq-total-decidable-Preorder =
    transitive-leq-Preorder preorder-total-decidable-Preorder

  leq-or-strict-greater-decidable-Preorder :
    (x y : element-total-decidable-Preorder) →
    UU (l1 ⊔ l2)
  leq-or-strict-greater-decidable-Preorder x y =
    leq-total-decidable-Preorder x y +
    strict-leq-total-decidable-Preorder y x

  helper-is-leq-or-strict-greater-total-decidable-Preorder :
    (x y : element-total-decidable-Preorder) →
    leq-total-decidable-Preorder x y +
    ¬ (leq-total-decidable-Preorder x y)
    → leq-or-strict-greater-decidable-Preorder x y
  helper-is-leq-or-strict-greater-total-decidable-Preorder x y (inl p) =
    inl p
  helper-is-leq-or-strict-greater-total-decidable-Preorder x y (inr p) =
    inr
      ( ( λ {refl → p (refl-leq-total-decidable-Preorder x)}) ,
         apply-universal-property-trunc-Prop
           ( is-total-preorder-total-decidable-Preorder y x)
           ( leq-total-decidable-preorder-Prop y x)
           ( ind-coprod
               ( λ _ → leq-total-decidable-Preorder y x)
               ( id)
               ( λ q → ex-falso (p q))))

  is-leq-or-strict-greater-total-decidable-Preorder :
    (x y : element-total-decidable-Preorder) →
    leq-or-strict-greater-decidable-Preorder x y
  is-leq-or-strict-greater-total-decidable-Preorder x y =
    helper-is-leq-or-strict-greater-total-decidable-Preorder
      ( x)
      ( y)
      ( is-decidable-leq-total-decidable-Preorder x y)
```

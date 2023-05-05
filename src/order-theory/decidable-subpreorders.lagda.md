# Decidable subpreorders

```agda
module order-theory.decidable-subpreorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
open import order-theory.subpreorders
```

</details>

## Idea

A **decidable subpreorder** of `P` is a decidable subtype of `P` equipped with
the restricted ordering of `P`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2)
  (S : type-Preorder X → Decidable-Prop l3)
  where

  type-Decidable-Subpreorder : UU (l1 ⊔ l3)
  type-Decidable-Subpreorder =
    type-Subpreorder X (subtype-decidable-subtype S)

  eq-type-Decidable-Subpreorder :
    (x y : type-Decidable-Subpreorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-type-Decidable-Subpreorder =
    eq-type-Subpreorder X (subtype-decidable-subtype S)

  leq-Decidable-Subpreorder-Prop :
    (x y : type-Decidable-Subpreorder) → Prop l2
  leq-Decidable-Subpreorder-Prop =
    leq-Subpreorder-Prop X (subtype-decidable-subtype S)

  leq-Decidable-Subpreorder : (x y : type-Decidable-Subpreorder) → UU l2
  leq-Decidable-Subpreorder =
    leq-Subpreorder X (subtype-decidable-subtype S)

  is-prop-leq-Decidable-Subpreorder :
    (x y : type-Decidable-Subpreorder) →
    is-prop (leq-Decidable-Subpreorder x y)
  is-prop-leq-Decidable-Subpreorder =
    is-prop-leq-Subpreorder X (subtype-decidable-subtype S)

  refl-leq-Decidable-Subpreorder :
    (x : type-Decidable-Subpreorder) → leq-Decidable-Subpreorder x x
  refl-leq-Decidable-Subpreorder =
    refl-leq-Subpreorder X (subtype-decidable-subtype S)

  transitive-leq-Decidable-Subpreorder :
    (x y z : type-Decidable-Subpreorder) →
    leq-Decidable-Subpreorder y z → leq-Decidable-Subpreorder x y →
    leq-Decidable-Subpreorder x z
  transitive-leq-Decidable-Subpreorder =
    transitive-leq-Subpreorder X (subtype-decidable-subtype S)

  preorder-Decidable-Subpreorder : Preorder (l1 ⊔ l3) l2
  preorder-Decidable-Subpreorder =
    preorder-Subpreorder X (subtype-decidable-subtype S)
```

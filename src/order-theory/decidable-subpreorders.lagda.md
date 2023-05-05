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

A **decidable subpreorder** of `P` is a decidable subtype of `P` equipped with the restricted ordering of `P`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2)
  (S : element-Preorder X → Decidable-Prop l3)
  where

  element-decidable-Subpreorder : UU (l1 ⊔ l3)
  element-decidable-Subpreorder =
    element-Subpreorder X (subtype-decidable-subtype S)

  eq-element-decidable-Subpreorder :
    (x y : element-decidable-Subpreorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-decidable-Subpreorder =
    eq-element-Subpreorder X (subtype-decidable-subtype S)

  leq-decidable-Subpreorder-Prop :
    (x y : element-decidable-Subpreorder) → Prop l2
  leq-decidable-Subpreorder-Prop =
    leq-Subpreorder-Prop X (subtype-decidable-subtype S)

  leq-decidable-Subpreorder : (x y : element-decidable-Subpreorder) → UU l2
  leq-decidable-Subpreorder =
    leq-Subpreorder X (subtype-decidable-subtype S)

  is-prop-leq-decidable-Subpreorder :
    (x y : element-decidable-Subpreorder) →
    is-prop (leq-decidable-Subpreorder x y)
  is-prop-leq-decidable-Subpreorder =
    is-prop-leq-Subpreorder X (subtype-decidable-subtype S)

  refl-leq-decidable-Subpreorder :
    (x : element-decidable-Subpreorder) → leq-decidable-Subpreorder x x
  refl-leq-decidable-Subpreorder =
    refl-leq-Subpreorder X (subtype-decidable-subtype S)

  transitive-leq-decidable-Subpreorder :
    (x y z : element-decidable-Subpreorder) →
    leq-decidable-Subpreorder y z → leq-decidable-Subpreorder x y →
    leq-decidable-Subpreorder x z
  transitive-leq-decidable-Subpreorder =
    transitive-leq-Subpreorder X (subtype-decidable-subtype S)

  decidable-Subpreorder : Preorder (l1 ⊔ l3) l2
  decidable-Subpreorder = Subpreorder X (subtype-decidable-subtype S)
```

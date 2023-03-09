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

A decidable subpreorder Q of P is a subpreorder Q of P such that for each element `x : P` it is decidable whether or not `x` is in `Q`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2)
  (S : element-Preorder X → decidable-Prop l3)
  where

  element-decidable-sub-Preorder : UU (l1 ⊔ l3)
  element-decidable-sub-Preorder =
    element-sub-Preorder X (subtype-decidable-subtype S)

  eq-element-decidable-sub-Preorder :
    (x y : element-decidable-sub-Preorder) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-decidable-sub-Preorder =
    eq-element-sub-Preorder X (subtype-decidable-subtype S)

  leq-decidable-sub-preorder-Prop :
    (x y : element-decidable-sub-Preorder) → Prop l2
  leq-decidable-sub-preorder-Prop =
    leq-sub-preorder-Prop X (subtype-decidable-subtype S)

  leq-decidable-sub-Preorder : (x y : element-decidable-sub-Preorder) → UU l2
  leq-decidable-sub-Preorder =
    leq-sub-Preorder X (subtype-decidable-subtype S)

  is-prop-leq-decidable-sub-Preorder :
    (x y : element-decidable-sub-Preorder) →
    is-prop (leq-decidable-sub-Preorder x y)
  is-prop-leq-decidable-sub-Preorder =
    is-prop-leq-sub-Preorder X (subtype-decidable-subtype S)

  refl-leq-decidable-sub-Preorder :
    (x : element-decidable-sub-Preorder) → leq-decidable-sub-Preorder x x
  refl-leq-decidable-sub-Preorder =
    refl-leq-sub-Preorder X (subtype-decidable-subtype S)

  transitive-leq-decidable-sub-Preorder :
    (x y z : element-decidable-sub-Preorder) →
    leq-decidable-sub-Preorder y z → leq-decidable-sub-Preorder x y →
    leq-decidable-sub-Preorder x z
  transitive-leq-decidable-sub-Preorder =
    transitive-leq-sub-Preorder X (subtype-decidable-subtype S)

  decidable-sub-Preorder : Preorder (l1 ⊔ l3) l2
  decidable-sub-Preorder = sub-Preorder X (subtype-decidable-subtype S)
```

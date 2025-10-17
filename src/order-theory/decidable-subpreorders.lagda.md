# Decidable subpreorders

```agda
module order-theory.decidable-subpreorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
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
Decidable-Subpreorder :
  {l1 l2 : Level} (l3 : Level) → Preorder l1 l2 → UU (l1 ⊔ lsuc l3)
Decidable-Subpreorder l3 P = decidable-subtype l3 (type-Preorder P)

module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (S : Decidable-Subpreorder l3 P)
  where

  type-Decidable-Subpreorder : UU (l1 ⊔ l3)
  type-Decidable-Subpreorder =
    type-Subpreorder P (subtype-decidable-subtype S)

  eq-type-Decidable-Subpreorder :
    (x y : type-Decidable-Subpreorder) → pr1 x ＝ pr1 y → x ＝ y
  eq-type-Decidable-Subpreorder =
    eq-type-Subpreorder P (subtype-decidable-subtype S)

  leq-Decidable-Subpreorder-Prop :
    (x y : type-Decidable-Subpreorder) → Prop l2
  leq-Decidable-Subpreorder-Prop =
    leq-Subpreorder-Prop P (subtype-decidable-subtype S)

  leq-Decidable-Subpreorder : (x y : type-Decidable-Subpreorder) → UU l2
  leq-Decidable-Subpreorder =
    leq-Subpreorder P (subtype-decidable-subtype S)

  is-prop-leq-Decidable-Subpreorder :
    (x y : type-Decidable-Subpreorder) →
    is-prop (leq-Decidable-Subpreorder x y)
  is-prop-leq-Decidable-Subpreorder =
    is-prop-leq-Subpreorder P (subtype-decidable-subtype S)

  refl-leq-Decidable-Subpreorder : is-reflexive leq-Decidable-Subpreorder
  refl-leq-Decidable-Subpreorder =
    refl-leq-Subpreorder P (subtype-decidable-subtype S)

  transitive-leq-Decidable-Subpreorder : is-transitive leq-Decidable-Subpreorder
  transitive-leq-Decidable-Subpreorder =
    transitive-leq-Subpreorder P (subtype-decidable-subtype S)

  preorder-Decidable-Subpreorder : Preorder (l1 ⊔ l3) l2
  preorder-Decidable-Subpreorder =
    preorder-Subpreorder P (subtype-decidable-subtype S)
```

# Decidable subposets

```agda
module order-theory.decidable-subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.subposets
```

</details>

## Idea

A **decidable subposet** of a poset `P` is a decidable subtype of `P`, equipped
with the restricted ordering of `P`.

## Definition

```agda
Decidable-Subposet :
  {l1 l2 : Level} (l3 : Level) → Poset l1 l2 → UU (l1 ⊔ lsuc l3)
Decidable-Subposet l3 P = decidable-subtype l3 (type-Poset P)

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (S : Decidable-Subposet l3 P)
  where

  type-Decidable-Subposet : UU (l1 ⊔ l3)
  type-Decidable-Subposet =
    type-Subposet P (subtype-decidable-subtype S)

  eq-type-Decidable-Subposet :
    (x y : type-Decidable-Subposet) → Id (pr1 x) (pr1 y) → x ＝ y
  eq-type-Decidable-Subposet =
    eq-type-Subposet P (subtype-decidable-subtype S)

  leq-Decidable-Subposet-Prop :
    (x y : type-Decidable-Subposet) → Prop l2
  leq-Decidable-Subposet-Prop =
    leq-Subposet-Prop P (subtype-decidable-subtype S)

  leq-Decidable-Subposet : (x y : type-Decidable-Subposet) → UU l2
  leq-Decidable-Subposet =
    leq-Subposet P (subtype-decidable-subtype S)

  is-prop-leq-Decidable-Subposet :
    (x y : type-Decidable-Subposet) →
    is-prop (leq-Decidable-Subposet x y)
  is-prop-leq-Decidable-Subposet =
    is-prop-leq-Subposet P (subtype-decidable-subtype S)

  refl-leq-Decidable-Subposet : is-reflexive leq-Decidable-Subposet
  refl-leq-Decidable-Subposet =
    refl-leq-Subposet P (subtype-decidable-subtype S)

  transitive-leq-Decidable-Subposet : is-transitive leq-Decidable-Subposet
  transitive-leq-Decidable-Subposet =
    transitive-leq-Subposet P (subtype-decidable-subtype S)

  poset-Decidable-Subposet : Poset (l1 ⊔ l3) l2
  poset-Decidable-Subposet = poset-Subposet P (subtype-decidable-subtype S)
```

# Decidable subposets

```agda
module order-theory.decidable-subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
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

A **decidable subposet** of a poset `P` is a decidable subtype of `P`, equipped with the restricted ordering of `P`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Poset l1 l2)
  (S : element-Poset X → Decidable-Prop l3)
  where

  element-decidable-Subposet : UU (l1 ⊔ l3)
  element-decidable-Subposet =
    element-Subposet X (subtype-decidable-subtype S)

  eq-element-decidable-Subposet :
    (x y : element-decidable-Subposet) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-decidable-Subposet =
    eq-element-Subposet X (subtype-decidable-subtype S)

  leq-decidable-Subposet-Prop :
    (x y : element-decidable-Subposet) → Prop l2
  leq-decidable-Subposet-Prop =
    leq-Subposet-Prop X (subtype-decidable-subtype S)

  leq-decidable-Subposet : (x y : element-decidable-Subposet) → UU l2
  leq-decidable-Subposet =
    leq-Subposet X (subtype-decidable-subtype S)

  is-prop-leq-decidable-Subposet :
    (x y : element-decidable-Subposet) →
    is-prop (leq-decidable-Subposet x y)
  is-prop-leq-decidable-Subposet =
    is-prop-leq-Subposet X (subtype-decidable-subtype S)

  refl-leq-decidable-Subposet :
    (x : element-decidable-Subposet) → leq-decidable-Subposet x x
  refl-leq-decidable-Subposet =
    refl-leq-Subposet X (subtype-decidable-subtype S)

  transitive-leq-decidable-Subposet :
    (x y z : element-decidable-Subposet) →
    leq-decidable-Subposet y z → leq-decidable-Subposet x y →
    leq-decidable-Subposet x z
  transitive-leq-decidable-Subposet =
    transitive-leq-Subposet X (subtype-decidable-subtype S)

  decidable-Subposet : Poset (l1 ⊔ l3) l2
  decidable-Subposet = Subposet X (subtype-decidable-subtype S)
```

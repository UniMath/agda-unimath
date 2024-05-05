# L-consistent theories

```agda
module modal-logic.l-consistent-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import modal-logic.axioms
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.weak-deduction

open import order-theory.maximal-elements-posets
open import order-theory.posets
open import order-theory.subposets
open import order-theory.subtypes-leq-posets
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} {i : Set l1}
  (logic : modal-theory l2 i)
  where

  is-L-consistent-theory-Prop :
    {l3 : Level} → modal-theory l3 i → Prop (l1 ⊔ l2 ⊔ l3)
  is-L-consistent-theory-Prop theory =
    is-consistent-modal-logic-Prop (weak-modal-logic-closure (logic ∪ theory))

  is-L-consistent-theory :
    {l3 : Level} → modal-theory l3 i → UU (l1 ⊔ l2 ⊔ l3)
  is-L-consistent-theory = type-Prop ∘ is-L-consistent-theory-Prop

  L-consistent-theory : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  L-consistent-theory l3 = type-subtype (is-L-consistent-theory-Prop {l3})

  modal-theory-L-consistent-theory :
    {l3 : Level} → L-consistent-theory l3 → modal-theory l3 i
  modal-theory-L-consistent-theory =
    inclusion-subtype is-L-consistent-theory-Prop

  is-L-consistent-theory-modal-theory-L-consistent-theory :
    {l3 : Level} (theory : L-consistent-theory l3) →
    is-L-consistent-theory (modal-theory-L-consistent-theory theory)
  is-L-consistent-theory-modal-theory-L-consistent-theory =
    is-in-subtype-inclusion-subtype is-L-consistent-theory-Prop

  is-consistent-closure-L-consistent-theory :
    {l3 : Level} (theory : L-consistent-theory l3) →
    is-consistent-modal-logic
      ( weak-modal-logic-closure (modal-theory-L-consistent-theory theory))
  is-consistent-closure-L-consistent-theory theory =
    is-consistent-modal-logic-antimonotic
      ( weak-modal-logic-closure (modal-theory-L-consistent-theory theory))
      ( weak-modal-logic-closure
        (logic ∪ modal-theory-L-consistent-theory theory))
      ( weak-modal-logic-closure-monotic
        ( subtype-union-right logic (modal-theory-L-consistent-theory theory)))
      ( is-L-consistent-theory-modal-theory-L-consistent-theory theory)

  is-consistent-modal-theory-L-consistent-theory :
    {l3 : Level} (theory : L-consistent-theory l3) →
    is-consistent-modal-logic (modal-theory-L-consistent-theory theory)
  is-consistent-modal-theory-L-consistent-theory theory =
    is-consistent-modal-logic-antimonotic
      ( modal-theory-L-consistent-theory theory)
      ( weak-modal-logic-closure (modal-theory-L-consistent-theory theory))
      ( subset-axioms-weak-modal-logic-closure)
      ( is-consistent-closure-L-consistent-theory theory)

  is-L-consistent-antimonotic :
    {l3 l4 : Level}
    (theory₁ : modal-theory l3 i) →
    (theory₂ : modal-theory l4 i) →
    theory₁ ⊆ theory₂ →
    is-L-consistent-theory theory₂ →
    is-L-consistent-theory theory₁
  is-L-consistent-antimonotic theory₁ theory₂ leq =
    is-consistent-modal-logic-antimonotic
      ( weak-modal-logic-closure (logic ∪ theory₁))
      ( weak-modal-logic-closure (logic ∪ theory₂))
      ( weak-modal-logic-closure-monotic
        ( subset-union-subset-right logic theory₁ theory₂ leq))

  L-consistent-theory-leq-Prop :
    {l3 : Level} → Relation-Prop (l1 ⊔ l3) (L-consistent-theory l3)
  L-consistent-theory-leq-Prop x y =
    leq-prop-subtype
      ( modal-theory-L-consistent-theory x)
      ( modal-theory-L-consistent-theory y)

  L-consistent-theory-leq :
    {l3 : Level} → Relation (l1 ⊔ l3) (L-consistent-theory l3)
  L-consistent-theory-leq = type-Relation-Prop L-consistent-theory-leq-Prop

  theories-Poset : (l3 : Level) → Poset (l1 ⊔ lsuc l3) (l1 ⊔ l3)
  theories-Poset l3 = subtypes-leq-Poset l3 (modal-formula i)

  L-consistent-theories-Poset :
    (l3 : Level) → Poset (l1 ⊔ l2 ⊔ lsuc l3) (l1 ⊔ l3)
  L-consistent-theories-Poset l3 =
    poset-Subposet (theories-Poset l3) (is-L-consistent-theory-Prop)

  module _
    (is-logic : is-weak-modal-logic logic)
    (is-cons : is-consistent-modal-logic logic)
    where

    is-L-consistent-theory-logic :
      is-L-consistent-theory logic
    is-L-consistent-theory-logic =
      is-consistent-modal-logic-antimonotic
        ( weak-modal-logic-closure (logic ∪ logic))
        ( logic)
        ( transitive-leq-subtype
          ( weak-modal-logic-closure (logic ∪ logic))
          ( weak-modal-logic-closure logic)
          ( logic)
          ( is-logic)
          ( weak-modal-logic-closure-monotic
            ( subtype-union-both logic logic logic
              ( refl-leq-subtype logic)
              ( refl-leq-subtype logic))))
        (is-cons)

    is-inhabited-L-consistent-theory : is-inhabited (L-consistent-theory l2)
    is-inhabited-L-consistent-theory =
      unit-trunc-Prop (logic , is-L-consistent-theory-logic)

module _
  {l1 : Level} {i : Set l1}
  where

  is-L-consistent-antimonotic-logic :
    {l2 l3 l4 : Level}
    (logic₁ : modal-theory l2 i) →
    (logic₂ : modal-theory l3 i) →
    (theory : modal-theory l4 i) →
    logic₁ ⊆ logic₂ →
    is-L-consistent-theory logic₂ theory →
    is-L-consistent-theory logic₁ theory
  is-L-consistent-antimonotic-logic logic₁ logic₂ theory leq =
    is-consistent-modal-logic-antimonotic
      ( weak-modal-logic-closure (logic₁ ∪ theory))
      ( weak-modal-logic-closure (logic₂ ∪ theory))
      ( weak-modal-logic-closure-monotic
        ( subset-union-subset-left logic₁ logic₂ theory leq))
```

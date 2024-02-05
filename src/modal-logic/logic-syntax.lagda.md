# Modal logic syntax

```agda
module modal-logic.logic-syntax where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import modal-logic.formulas
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 : Level} (l2 : Level) (i : Set l1)
  where

  formulas : UU (l1 ⊔ lsuc l2)
  formulas = subtype l2 (formula i)

module _
  {l1 l2 : Level} {i : Set l1}
  where

  infix 5 _⊢_

  data _⊢_ (axioms : formulas l2 i) : formula i → UU (l1 ⊔ l2) where
    ax : {a : formula i} → is-in-subtype axioms a → axioms ⊢ a
    mp : {a b : formula i} → axioms ⊢ a ⇒ b → axioms ⊢ a → axioms ⊢ b
    nec : {a : formula i} → axioms ⊢ a → axioms ⊢ □ a

  modal-logic : formulas l2 i → formulas (l1 ⊔ l2) i
  modal-logic axioms a = trunc-Prop (axioms ⊢ a)

  is-contradictory-modal-logic-Prop : formulas l2 i → Prop l2
  is-contradictory-modal-logic-Prop logic = logic ⊥

  is-contradictory-modal-logic : formulas l2 i → UU l2
  is-contradictory-modal-logic = type-Prop ∘ is-contradictory-modal-logic-Prop

  is-consistent-modal-logic-Prop : formulas l2 i → Prop l2
  is-consistent-modal-logic-Prop = neg-Prop ∘ is-contradictory-modal-logic-Prop

  is-consistent-modal-logic : formulas l2 i → UU l2
  is-consistent-modal-logic = type-Prop ∘ is-consistent-modal-logic-Prop

module _
  {l1 l2 : Level} {i : Set l1} {axioms : formulas l2 i}
  where

  modal-logic-ax :
    {a : formula i} →
    is-in-subtype axioms a →
    is-in-subtype (modal-logic axioms) a
  modal-logic-ax = unit-trunc-Prop ∘ ax

  modal-logic-mp :
    {a b : formula i} →
    is-in-subtype (modal-logic axioms) (a ⇒ b) →
    is-in-subtype (modal-logic axioms) a →
    is-in-subtype (modal-logic axioms) b
  modal-logic-mp {a} {b} tdab tda =
    apply-twice-universal-property-trunc-Prop tdab tda
      ( modal-logic axioms b)
      ( λ dab da → unit-trunc-Prop (mp dab da))

  modal-logic-nec :
    {a : formula i} →
    is-in-subtype (modal-logic axioms) a →
    is-in-subtype (modal-logic axioms) (□ a)
  modal-logic-nec {a} =
    map-universal-property-trunc-Prop
      ( modal-logic axioms (□ a))
      ( λ da → unit-trunc-Prop (nec da))

module _
  {l1 : Level} {i : Set l1}
  where

  axioms-subset-modal-logic :
    {l2 : Level} (axioms : formulas l2 i) → axioms ⊆ modal-logic axioms
  axioms-subset-modal-logic _ a H = unit-trunc-Prop (ax H)

  modal-logic-closed :
    {l2 : Level} {axioms : formulas l2 i} {a : formula i} →
    modal-logic axioms ⊢ a →
    is-in-subtype (modal-logic axioms) a
  modal-logic-closed (ax x) = x
  modal-logic-closed {axioms = axioms} {a} (mp tdab tda) =
    apply-twice-universal-property-trunc-Prop
      ( modal-logic-closed tdab)
      ( modal-logic-closed tda)
      ( modal-logic axioms a)
      (λ dab da → unit-trunc-Prop (mp dab da))
  modal-logic-closed {axioms = axioms} {a} (nec d) =
    apply-universal-property-trunc-Prop
      ( modal-logic-closed d)
      ( modal-logic axioms a)
      ( unit-trunc-Prop ∘ nec)

  subset-double-modal-logic :
    {l2 : Level}
    (axioms : formulas l2 i) →
    modal-logic (modal-logic axioms) ⊆ modal-logic axioms
  subset-double-modal-logic axioms a =
    map-universal-property-trunc-Prop
      ( modal-logic axioms a)
      ( modal-logic-closed)

  modal-logic-idempotent :
    {l2 : Level}
    (axioms : formulas l2 i) →
    modal-logic axioms ＝ modal-logic (modal-logic axioms)
  modal-logic-idempotent axioms =
    antisymmetric-leq-subtype _ _
      ( axioms-subset-modal-logic (modal-logic axioms))
      ( subset-double-modal-logic axioms)

module _
  {l1 l2 l3 : Level} {i : Set l1} {ax₁ : formulas l2 i} {ax₂ : formulas l3 i}
  (leq : ax₁ ⊆ ax₂)
  where

  deduction-monotic : {a : formula i} → ax₁ ⊢ a → ax₂ ⊢ a
  deduction-monotic (ax x) = ax (leq _ x)
  deduction-monotic (mp dab da) =
    mp (deduction-monotic dab) (deduction-monotic da)
  deduction-monotic (nec d) = nec (deduction-monotic d)

  modal-logic-monotic : modal-logic ax₁ ⊆ modal-logic ax₂
  modal-logic-monotic a =
    map-universal-property-trunc-Prop
      ( modal-logic ax₂ a)
      ( unit-trunc-Prop ∘ deduction-monotic)

module _
  {l1 l2 l3 : Level} {i : Set l1} {ax₁ : formulas l2 i} {ax₂ : formulas l3 i}
  where

  subset-modal-logic-if-subset-axioms :
    ax₁ ⊆ modal-logic ax₂ → modal-logic ax₁ ⊆ modal-logic ax₂
  subset-modal-logic-if-subset-axioms leq =
    transitive-leq-subtype
      ( modal-logic ax₁)
      ( modal-logic (modal-logic ax₂))
      ( modal-logic ax₂)
      ( subset-double-modal-logic ax₂)
      ( modal-logic-monotic leq)

module _
  {l1 l2 : Level} {i : Set l1} (a : formula i) (logic : formulas l2 i)
  where

  theory-add-formula : formulas (l1 ⊔ l2) i
  theory-add-formula = union-subtype (Id-formula-Prop a) logic

  formula-in-add-formula : is-in-subtype theory-add-formula a
  formula-in-add-formula = subtype-union-left (Id-formula-Prop a) logic a refl

  subset-add-formula : logic ⊆ theory-add-formula
  subset-add-formula = subtype-union-right (Id-formula-Prop a) logic
```

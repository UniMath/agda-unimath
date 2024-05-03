# Modal logic syntax

```agda
module modal-logic.logic-syntax where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.coproduct-types
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

  modal-theory : UU (l1 ⊔ lsuc l2)
  modal-theory = subtype l2 (formula i)

  -- TODO: remove
  formulas : UU (l1 ⊔ lsuc l2)
  formulas = modal-theory

module _
  {l1 l2 : Level} {i : Set l1}
  where

  infix 5 _⊢_

  data _⊢_ (axioms : modal-theory l2 i) : formula i → UU (l1 ⊔ l2) where
    ax : {a : formula i} → is-in-subtype axioms a → axioms ⊢ a
    mp : {a b : formula i} → axioms ⊢ a →ₘ b → axioms ⊢ a → axioms ⊢ b
    nec : {a : formula i} → axioms ⊢ a → axioms ⊢ □ a

  -- TODO: rename to modal-logic-closure
  modal-logic : modal-theory l2 i → modal-theory (l1 ⊔ l2) i
  modal-logic axioms a = trunc-Prop (axioms ⊢ a)

  is-modal-logic-Prop : modal-theory l2 i → Prop (l1 ⊔ l2)
  is-modal-logic-Prop theory =
    leq-prop-subtype (modal-logic theory) theory

  is-modal-logic : modal-theory l2 i → UU (l1 ⊔ l2)
  is-modal-logic = type-Prop ∘ is-modal-logic-Prop

  is-contradictory-modal-logic-Prop : modal-theory l2 i → Prop l2
  is-contradictory-modal-logic-Prop logic = logic ⊥

  is-contradictory-modal-logic : modal-theory l2 i → UU l2
  is-contradictory-modal-logic = type-Prop ∘ is-contradictory-modal-logic-Prop

  is-consistent-modal-logic-Prop : modal-theory l2 i → Prop l2
  is-consistent-modal-logic-Prop = neg-Prop ∘ is-contradictory-modal-logic-Prop

  is-consistent-modal-logic : modal-theory l2 i → UU l2
  is-consistent-modal-logic = type-Prop ∘ is-consistent-modal-logic-Prop

module _
  {l1 : Level} {i : Set l1}
  where

  is-contradictory-modal-logic-monotic :
    {l2 l3 : Level} (ax₁ : modal-theory l2 i) (ax₂ : modal-theory l3 i) →
    ax₁ ⊆ ax₂ →
    is-contradictory-modal-logic ax₁ →
    is-contradictory-modal-logic ax₂
  is-contradictory-modal-logic-monotic ax₁ ax₂ leq = leq ⊥

  is-consistent-modal-logic-antimonotic :
    {l2 l3 : Level} (ax₁ : modal-theory l2 i) (ax₂ : modal-theory l3 i) →
    ax₁ ⊆ ax₂ →
    is-consistent-modal-logic ax₂ →
    is-consistent-modal-logic ax₁
  is-consistent-modal-logic-antimonotic ax₁ ax₂ leq is-cons =
    is-cons ∘ is-contradictory-modal-logic-monotic ax₁ ax₂ leq

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
    is-in-subtype (modal-logic axioms) (a →ₘ b) →
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
  modal-logic-closed (mp dab da) =
    modal-logic-mp (modal-logic-closed dab) (modal-logic-closed da)
  modal-logic-closed (nec d) =
    modal-logic-nec (modal-logic-closed d)

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
  {l1 l2 : Level} {i : Set l1} (a : formula i) (theory : modal-theory l2 i)
  where

  -- TODO: make Id-formula to be a function for 1 element modal-theory
  theory-add-formula : formulas (l1 ⊔ l2) i
  theory-add-formula = (Id-formula-Prop a) ∪ theory

  formula-in-add-formula : is-in-subtype theory-add-formula a
  formula-in-add-formula = subtype-union-left (Id-formula-Prop a) theory a refl

  subset-add-formula : theory ⊆ theory-add-formula
  subset-add-formula = subtype-union-right (Id-formula-Prop a) theory

  elim-theory-add-formula :
    {l3 : Level} (P : formula i → Prop l3) →
    type-Prop (P a) →
    ((x : formula i) → is-in-subtype theory x → type-Prop (P x)) →
    (x : formula i) → is-in-subtype theory-add-formula x → type-Prop (P x)
  elim-theory-add-formula P H-a H-rest =
    elim-union-subtype (Id-formula-Prop a) theory P
      ( λ { .a refl → H-a })
      ( H-rest)

  subset-theory-add-formula :
    {l3 : Level} (theory' : formulas l3 i) →
    is-in-subtype theory' a →
    theory ⊆ theory' →
    theory-add-formula ⊆ theory'
  subset-theory-add-formula theory' a-in =
    subtype-union-both
      ( Id-formula-Prop a)
      ( theory)
      ( theory')
      ( λ { .a refl → a-in })

module _
  {l1 : Level} {i : Set l1}
  where

  is-disjuctive-modal-theory :
    {l2 : Level} → modal-theory l2 i → UU (l1 ⊔ l2)
  is-disjuctive-modal-theory theory =
    (a : formula i) → is-in-subtype theory a + is-in-subtype theory (~ a)

  theory-add-formula-union-right :
    (a : formula i)
    {l2 l3 : Level}
    (theory : formulas l2 i)
    (theory' : formulas l3 i) →
    theory ∪ theory-add-formula a theory' ⊆
      theory-add-formula a (theory ∪ theory')
  theory-add-formula-union-right a theory theory' =
    union-swap-1-2 theory (Id-formula-Prop a) theory'

  inv-theory-add-formula-union-right :
    (a : formula i)
    {l2 l3 : Level}
    (theory : formulas l2 i)
    (theory' : formulas l3 i) →
    theory-add-formula a (theory ∪ theory') ⊆
      theory ∪ theory-add-formula a theory'
  inv-theory-add-formula-union-right a theory theory' =
    union-swap-1-2 (Id-formula-Prop a) theory theory'
```

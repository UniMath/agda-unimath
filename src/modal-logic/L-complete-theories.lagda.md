# L-complete theories

```agda
module modal-logic.L-complete-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
-- open import foundation.cartesian-product-types
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
-- open import foundation.empty-types
-- open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
-- open import foundation.inhabited-types
-- open import foundation.intersections-subtypes
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negation
-- open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.propositions
-- open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
-- open import foundation.unit-type
open import foundation.universe-levels

-- open import foundation-core.equivalences

-- open import lists.lists
-- open import lists.reversing-lists

open import modal-logic.axioms
-- open import modal-logic.completeness
open import modal-logic.formulas
-- open import modal-logic.formulas-deduction
-- open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
-- open import modal-logic.modal-logic-K
-- open import modal-logic.soundness
open import modal-logic.weak-deduction

-- open import order-theory.chains-posets
open import order-theory.maximal-elements-posets
open import order-theory.posets
-- open import order-theory.preorders
open import order-theory.subposets
open import order-theory.subtypes-leq-posets
-- open import order-theory.top-elements-posets
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} {i : Set l1}
  (logic : modal-theory l2 i)
  (logic-is-modal-logic : is-modal-logic logic)
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

  is-L-consistent-antimonotic :
    {l3 l4 : Level}
    (theory₁ : modal-theory l3 i) →
    (theory₂ : modal-theory l4 i) →
    theory₁ ⊆ theory₂ →
    is-L-consistent-theory theory₂ →
    is-L-consistent-theory theory₁
  is-L-consistent-antimonotic theory₁ theory₂ leq is-cons =
    is-consistent-modal-logic-antimonotic
      ( weak-modal-logic-closure (logic ∪ theory₁))
      ( weak-modal-logic-closure (logic ∪ theory₂))
      ( weak-modal-logic-closure-monotic
        ( subset-union-subset-right logic theory₁ theory₂ leq))
      ( is-cons)

  L-consistent-theory-leq-Prop :
    {l3 : Level} → Relation-Prop (l1 ⊔ l3) (L-consistent-theory l3)
    -- {l3 : Level} → L-consistent-theory l3 → L-consistent-theory → Prop (l1 ⊔ l2)
  L-consistent-theory-leq-Prop x y =
    leq-prop-subtype
      ( modal-theory-L-consistent-theory x)
      ( modal-theory-L-consistent-theory y)

  L-consistent-theory-leq :
    {l3 : Level} → Relation (l1 ⊔ l3) (L-consistent-theory l3)
  L-consistent-theory-leq = type-Relation-Prop L-consistent-theory-leq-Prop

  theories-Poset : (l3 : Level) → Poset (l1 ⊔ lsuc l3) (l1 ⊔ l3)
  theories-Poset l3 = subtypes-leq-Poset l3 (formula i)

  L-consistent-theories-Poset :
    (l3 : Level) → Poset (l1 ⊔ l2 ⊔ lsuc l3) (l1 ⊔ l3)
  L-consistent-theories-Poset l3 =
    poset-Subposet (theories-Poset l3) (is-L-consistent-theory-Prop)

  is-L-complete-theory-Prop :
    {l3 : Level} → L-consistent-theory l3 → Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-L-complete-theory-Prop {l3} =
    is-maximal-element-Poset-Prop (L-consistent-theories-Poset l3)

  is-L-complete-theory :
    {l3 : Level} → L-consistent-theory l3 → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-L-complete-theory = type-Prop ∘ is-L-complete-theory-Prop

  L-complete-theory : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  L-complete-theory l3 = type-subtype (is-L-complete-theory-Prop {l3})

  L-consistent-theory-L-complete-theory :
    {l3 : Level} → L-complete-theory l3 → L-consistent-theory l3
  L-consistent-theory-L-complete-theory = inclusion-subtype is-L-complete-theory-Prop

  is-L-complete-theory-L-consistent-theory :
    {l3 : Level} (theory : L-complete-theory l3) →
    is-L-complete-theory (L-consistent-theory-L-complete-theory theory)
  is-L-complete-theory-L-consistent-theory =
    is-in-subtype-inclusion-subtype is-L-complete-theory-Prop

  modal-theory-L-complete-theory :
    {l3 : Level} → L-complete-theory l3 → modal-theory l3 i
  modal-theory-L-complete-theory =
    modal-theory-L-consistent-theory ∘ L-consistent-theory-L-complete-theory

  eq-is-L-consistent-union-L-complete :
    {l3 l4 : Level} →
    (((theory , _) , _) : L-complete-theory (l1 ⊔ l2 ⊔ l3 ⊔ l4)) →
    (theory' : modal-theory l4 i) →
    is-L-consistent-theory (theory' ∪ theory) →
    theory' ∪ theory ＝ theory
  eq-is-L-consistent-union-L-complete
    ((theory , is-cons) , is-comp) theory' is-L-cons =
      ap
        ( modal-theory-L-consistent-theory)
        ( is-comp
          ( theory' ∪ theory , is-L-cons)
          ( subtype-union-right theory' theory))

  union-L-consistent :
    {l3 : Level} →
    L-consistent-theory l3 →
    L-consistent-theory (l1 ⊔ l2 ⊔ l3)
  pr1 (union-L-consistent (theory , is-cons)) =
    weak-modal-logic-closure (logic ∪ theory)
  pr2 (union-L-consistent (theory , is-cons)) bot-in-logic =
    is-cons
      ( transitive-leq-subtype
        ( weak-modal-logic-closure
          ( logic ∪ weak-modal-logic-closure (logic ∪ theory)))
        ( weak-modal-logic-closure (weak-modal-logic-closure (logic ∪ theory)))
        ( weak-modal-logic-closure (logic ∪ theory))
        ( is-weak-modal-logic-weak-modal-logic-closure)
        ( weak-modal-logic-closure-monotic
          ( subtype-union-both
            ( logic)
            ( weak-modal-logic-closure (logic ∪ theory))
            ( weak-modal-logic-closure (logic ∪ theory))
            ( transitive-leq-subtype
              ( logic)
              ( logic ∪ theory)
              ( weak-modal-logic-closure (logic ∪ theory))
              ( subset-axioms-weak-modal-logic)
              ( subtype-union-left logic theory))
            ( refl-leq-subtype (weak-modal-logic-closure (logic ∪ theory)))))
        ( ⊥)
        ( bot-in-logic))

  module _
    {l3 : Level}
    (t@((theory , is-cons) , is-comp) : L-complete-theory (l1 ⊔ l2 ⊔ l3))
    where

    eq-union-L-consistent :
      weak-modal-logic-closure (logic ∪ theory) ＝ theory
    eq-union-L-consistent =
      ap modal-theory-L-consistent-theory
        ( is-comp
          ( union-L-consistent (theory , is-cons))
          ( transitive-leq-subtype
            ( theory)
            ( logic ∪ theory)
            ( weak-modal-logic-closure (logic ∪ theory))
            ( subset-axioms-weak-modal-logic)
            ( subtype-union-right logic theory)))

    subset-union-L-consistent :
      weak-modal-logic-closure (logic ∪ theory) ⊆ theory
    subset-union-L-consistent =
      inv-tr
        ( _⊆ theory)
        ( eq-union-L-consistent)
        ( refl-leq-subtype theory)

    subset-union-logic-L-complete-theory :
      logic ∪ theory ⊆ theory
    subset-union-logic-L-complete-theory =
      transitive-leq-subtype
        ( logic ∪ theory)
        ( modal-theory-L-consistent-theory
          ( union-L-consistent (theory , is-cons)))
        ( theory)
        ( subset-union-L-consistent)
        ( subset-axioms-weak-modal-logic)

    subset-logic-L-complete-theory :
      logic ⊆ theory
    subset-logic-L-complete-theory =
      transitive-leq-subtype
        ( logic)
        ( logic ∪ theory)
        ( theory)
        ( subset-union-logic-L-complete-theory)
        ( subtype-union-left logic theory)

    is-weak-modal-logic-L-complete-theory :
      is-weak-modal-logic theory
    is-weak-modal-logic-L-complete-theory =
      transitive-leq-subtype
        ( weak-modal-logic-closure theory)
        ( modal-theory-L-consistent-theory
          ( union-L-consistent (theory , is-cons)))
        ( theory)
        ( subset-union-L-consistent)
        ( weak-modal-logic-closure-monotic (subtype-union-right logic theory))

    module _
      (contains-ax-k : ax-k i ⊆ logic)
      (contains-ax-s : ax-s i ⊆ logic)
      (contains-ax-dn : ax-dn i ⊆ logic)
      where

      private
        contains-ax-k' : ax-k i ⊆ theory
        contains-ax-k' =
          transitive-leq-subtype (ax-k i) logic theory
            ( subset-logic-L-complete-theory)
            ( contains-ax-k)

        contains-ax-s' : ax-s i ⊆ theory
        contains-ax-s' =
          transitive-leq-subtype (ax-s i) logic theory
            ( subset-logic-L-complete-theory)
            ( contains-ax-s)

        contains-ax-dn' : ax-dn i ⊆ theory
        contains-ax-dn' =
          transitive-leq-subtype (ax-dn i) logic theory
            ( subset-logic-L-complete-theory)
            ( contains-ax-dn)

      is-L-consistent-add-formula-not-in-logic :
        {a : formula i} →
        ¬ (is-in-subtype theory a) →
        is-L-consistent-theory (theory-add-formula (~ a) theory)
      is-L-consistent-add-formula-not-in-logic {a} not-in-logic bot-in-logic =
        not-in-logic
          ( weak-modal-logic-mp theory
            ( is-weak-modal-logic-L-complete-theory)
            ( contains-ax-dn' (~~ a →ₘ a) (a , refl))
            ( is-weak-modal-logic-L-complete-theory (~~ a)
              ( forward-implication
                ( deduction-lemma
                  ( theory)
                  ( contains-ax-k')
                  ( contains-ax-s')
                  ( ~ a)
                  ( ⊥))
                ( weak-modal-logic-closure-monotic
                  ( subtype-union-both logic (theory-add-formula (~ a) theory)
                    ( theory-add-formula (~ a) theory)
                    ( transitive-leq-subtype
                      ( logic)
                      ( theory)
                      ( theory-add-formula (~ a) theory)
                      ( subset-add-formula (~ a) theory)
                      ( subset-logic-L-complete-theory))
                    ( refl-leq-subtype (theory-add-formula (~ a) theory)))
                  ( ⊥)
                  ( bot-in-logic)))))

      contains-negation-not-contains-formula-L-complete-theory :
        {a : formula i} →
        ¬ (is-in-subtype theory a) →
        is-in-subtype theory (~ a)
      contains-negation-not-contains-formula-L-complete-theory {a} not-in-logic =
          tr
            ( λ t → is-in-subtype t (~ a))
            ( eq-is-L-consistent-union-L-complete
              {l3 = l3} {l4 = l1}
              ( t)
              ( Id-formula-Prop (~ a))
              ( is-L-consistent-add-formula-not-in-logic not-in-logic))
            ( formula-in-add-formula (~ a) theory)

      is-disjuctive-L-complete-theory :
        LEM (l1 ⊔ l2 ⊔ l3) →
        is-disjuctive-modal-theory theory
      is-disjuctive-L-complete-theory lem a with lem (theory a)
      ... | inl a-in-logic = inl a-in-logic
      ... | inr a-not-in-logic =
        inr
          ( contains-negation-not-contains-formula-L-complete-theory
            ( a-not-in-logic))
```

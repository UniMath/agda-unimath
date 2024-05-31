# Finite approximability

```agda
module modal-logic.finite-approximability where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.law-of-excluded-middle
open import foundation.propositional-resizing
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import modal-logic.closed-under-subformulas-theories
open import modal-logic.completeness
open import modal-logic.completeness-k
open import modal-logic.completeness-s5
open import modal-logic.decision-procedure
open import modal-logic.deduction
open import modal-logic.kripke-models-filtrations
open import modal-logic.kripke-semantics
open import modal-logic.modal-logic-k
open import modal-logic.modal-logic-s5
open import modal-logic.soundness
open import modal-logic.subformulas

open import order-theory.zorn

open import univalent-combinatorics.finite-types
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 : Level} (i : Set l1)
  where
  is-finitely-approximable-Prop :
    {l2 : Level} (l3 l4 l5 l6 : Level) →
    modal-theory l2 i →
    Prop (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ lsuc l6)
  is-finitely-approximable-Prop l3 l4 l5 l6 logic =
    exists-structure-Prop
      ( model-class l3 l4 i l5 l6)
      ( λ C →
        ( C ⊆ finite-kripke-models l3 l4 i l5) ×
        ( soundness logic C) ×
        ( completeness logic C))

  is-finitely-approximable :
    {l2 : Level} (l3 l4 l5 l6 : Level) →
    modal-theory l2 i →
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ lsuc l6)
  is-finitely-approximable l3 l4 l5 l6 logic =
    type-Prop (is-finitely-approximable-Prop l3 l4 l5 l6 logic)

  module _
    {l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level}
    (C : model-class l2 l3 i l4 l5)
    (filtration : modal-theory l1 i →
                  kripke-model l2 l3 i l4 →
                  kripke-model l6 l7 i l8)
    (is-filtration :
      ((M , _) : type-subtype C) (theory : modal-theory l1 i) →
      is-modal-theory-closed-under-subformulas theory →
      is-kripke-model-filtration theory M (filtration theory M))
    (logic : modal-theory l9 i)
    (complete : completeness logic C)
    (C₂ : model-class l6 l7 i l8 l10)
    (leq : filtrate-class i C filtration ⊆ C₂)
    (sound : soundness logic C₂)
    where

    is-finitely-approximable-filtration :
      LEM (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4) →
      is-finitely-approximable l6 l7 l8
        (l1 ⊔ l5 ⊔ lsuc (l2 ⊔ l3 ⊔ l4 ⊔ l6 ⊔ l7 ⊔ l8)) logic
    is-finitely-approximable-filtration lem =
      intro-exists (filtrate-class i C filtration)
        ( triple
          ( is-finite-filtrate-class i C filtration is-filtration lem)
          ( filtrate-soundness i C filtration logic C₂ leq sound)
          ( filtrate-completeness i C filtration is-filtration logic complete))

  module _
    (lem : LEM (lsuc (lsuc l1)))
    (zorn : Zorn (lsuc l1) l1 l1)
    (prop-resize : propositional-resizing l1 (lsuc l1))
    where

    is-finitely-approximable-K :
      is-finitely-approximable
        ( lsuc (lsuc l1))
        ( lsuc l1)
        ( lsuc l1)
        ( lsuc (lsuc (lsuc l1)))
        ( modal-logic-K i)
    is-finitely-approximable-K =
      is-finitely-approximable-filtration
        ( all-models (lsuc l1) l1 i l1)
        ( minimal-kripke-model-filtration)
        ( λ (M , _) theory is-closed →
          ( is-kripke-model-filtration-minimal-kripke-model-filtration
            ( theory)
            ( M)
            ( is-closed)))
        ( modal-logic-K i)
        ( completeness-K i (lower-LEM (lsuc (lsuc l1)) lem) zorn prop-resize)
        ( all-models (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1))
        ( λ _ _ → star)
        ( transitive-leq-subtype
          ( modal-logic-K i)
          ( class-modal-logic
            ( decidable-kripke-models (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1)))
          ( class-modal-logic
            ( all-models (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1)))
          ( class-modal-logic-monotic
            ( all-models (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1))
            ( decidable-kripke-models (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1))
            ( all-models-is-decidable i lem))
          ( soundness-K i))
        ( lem)

    is-finitely-approximable-S5 :
      is-finitely-approximable
        ( lsuc (lsuc l1))
        ( lsuc (lsuc l1))
        ( lsuc l1)
        ( lsuc (lsuc (lsuc l1)))
        ( modal-logic-S5 i)
    is-finitely-approximable-S5 =
      is-finitely-approximable-filtration
        ( equivalence-kripke-models (lsuc l1) l1 i l1)
        ( minimal-transitive-kripke-model-filtration)
        ( λ (M , in-equiv) theory is-closed →
          ( is-filtration-minimal-transitive-kripke-model-filtration
            ( theory)
            ( M)
            ( is-closed)
            ( pr2 (pr2 in-equiv)))) -- TODO: refactor
        ( modal-logic-S5 i)
        ( completeness-S5 i (lower-LEM (lsuc (lsuc l1)) lem) zorn prop-resize)
        ( equivalence-kripke-models
          (lsuc (lsuc l1)) (lsuc (lsuc l1)) i (lsuc l1))
        ( λ M* →
          ( elim-exists
            ( equivalence-kripke-models
              (lsuc (lsuc l1)) (lsuc (lsuc l1)) i (lsuc l1) M*)
            ( λ where
              ( a , M , in-equiv) refl →
                ( minimal-transitive-filtration-preserves-equivalence
                  ( subformulas a)
                  ( M)
                  ( is-modal-theory-closed-under-subformulas-subformulas a)
                  ( in-equiv)))))
        ( transitive-leq-subtype
          ( modal-logic-S5 i)
          ( class-modal-logic
            ( decidable-subclass i
              ( equivalence-kripke-models
                (lsuc (lsuc l1)) (lsuc (lsuc l1)) i (lsuc l1))))
          ( class-modal-logic
            ( equivalence-kripke-models
              (lsuc (lsuc l1)) (lsuc (lsuc l1)) i (lsuc l1)))
          ( class-modal-logic-monotic
            ( equivalence-kripke-models
              (lsuc (lsuc l1)) (lsuc (lsuc l1)) i (lsuc l1))
            ( decidable-subclass i
              ( equivalence-kripke-models
                (lsuc (lsuc l1)) (lsuc (lsuc l1)) i (lsuc l1)))
            ( subset-decidable-subclass-lem i lem
              ( equivalence-kripke-models
                (lsuc (lsuc l1)) (lsuc (lsuc l1)) i (lsuc l1))))
          ( soundness-S5 i))
        ( lem)
```

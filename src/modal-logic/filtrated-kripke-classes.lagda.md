# Filtrated Kripke Classes

```agda
module modal-logic.filtrated-kripke-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.existential-quantification
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import lists.lists-subtypes

open import modal-logic.closed-under-subformulas-theories
open import modal-logic.completeness
open import modal-logic.deduction
open import modal-logic.filtration-lemma
open import modal-logic.formulas
open import modal-logic.kripke-models-filtrations
open import modal-logic.kripke-semantics
open import modal-logic.soundness
open import modal-logic.subformulas

open import univalent-combinatorics.finite-types
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} (i : Set l3)
  (C : model-class l1 l2 i l4 l5)
  (filtration : modal-theory l3 i →
                kripke-model l1 l2 i l4 →
                kripke-model l6 l7 i l8)
  where

  filtrate-class :
    model-class l6 l7 i l8 ( l3 ⊔ l5 ⊔ lsuc (l1 ⊔ l2 ⊔ l4 ⊔ l6 ⊔ l7 ⊔ l8))
  filtrate-class M* =
    exists-structure-Prop (modal-formula i × type-subtype C)
      ( λ (a , M , _) → M* ＝ filtration (subformulas a) M)

  module _
    (filtration-is-filtration :
      ((M , _) : type-subtype C)
      (theory : modal-theory l3 i) →
      is-modal-theory-closed-under-subformulas theory →
      is-kripke-model-filtration theory M (filtration theory M))
    where

    is-finite-filtrate-class :
      LEM (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4)) →
      filtrate-class ⊆ finite-kripke-models l6 l7 i l8
    is-finite-filtrate-class lem M* =
      elim-exists
        ( finite-kripke-models l6 l7 i l8 M*)
        ( λ where
          (a , M , M-in-C) refl →
            ( is-finite-equiv
              ( equiv-is-kripke-model-filtration
                ( subformulas a)
                ( M)
                ( M*)
                ( filtration-is-filtration
                  ( M , M-in-C)
                  ( subformulas a)
                  ( is-modal-theory-closed-under-subformulas-subformulas a)))
              ( is-finite-equivalence-classes-filtration i M lem
                ( subformulas a)
                ( is-finite-subformulas-list
                  ( lower-LEM (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4)) lem)
                ( a)))))

    filtrate-completeness :
      {l9 : Level} (logic : modal-theory l9 i) →
      completeness logic C →
      completeness logic filtrate-class
    filtrate-completeness logic complete a in-logic =
      complete a
        ( λ M M-in-class x →
          ( backward-implication
            ( filtration-lemma
              ( subformulas a)
              ( is-modal-theory-closed-under-subformulas-subformulas a)
              ( M)
              ( filtration (subformulas a) M)
              ( filtration-is-filtration
                ( M , M-in-class)
                ( subformulas a)
                ( is-modal-theory-closed-under-subformulas-subformulas a))
              ( a)
              ( head-in-list-subtype)
              ( x))
            ( in-logic
              ( filtration (subformulas a) M)
              ( intro-exists (a , M , M-in-class) refl)
              ( map-equiv-is-kripke-model-filtration
                ( subformulas a)
                ( M)
                ( filtration (subformulas a) M)
                ( filtration-is-filtration
                  ( M , M-in-class)
                  ( subformulas a)
                  ( is-modal-theory-closed-under-subformulas-subformulas a))
                ( class (Φ-equivalence (subformulas a) M) x)))))

  filtrate-soundness :
    {l9 l10 : Level} (logic : modal-theory l9 i) →
    (C₂ : model-class l6 l7 i l8 l10) →
    filtrate-class ⊆ C₂ →
    soundness logic C₂ →
    soundness logic filtrate-class
  filtrate-soundness logic C₂ H =
    transitive-leq-subtype
      ( logic)
      ( class-modal-logic C₂)
      ( class-modal-logic filtrate-class)
      ( class-modal-logic-monotic filtrate-class C₂ H)
```

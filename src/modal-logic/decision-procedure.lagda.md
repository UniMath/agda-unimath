# Modal logic decision

```agda
module modal-logic.decision-procedure where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions

open import lists.arrays
open import lists.concatenation-lists
open import lists.lists
open import lists.lists-subtypes
open import lists.reversing-lists

open import modal-logic.closed-under-subformulas-theories
open import modal-logic.completeness
open import modal-logic.deduction
open import modal-logic.filtration-lemma
open import modal-logic.formulas
open import modal-logic.kripke-models-filtrations
open import modal-logic.kripke-semantics
open import modal-logic.soundness
open import modal-logic.subformulas
open import modal-logic.weak-deduction

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.kuratowsky-finite-sets
open import univalent-combinatorics.small-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l3 l4 l5 l6 : Level}
  (i : Set l1)
  (C : model-class l3 l4 i l5 l6)
  (C-sub-fin : C ⊆ finite-decidable-kripke-models l3 l4 i l5)
  (C-is-fin : is-finite (type-subtype C))
  where

  decision-procedure' :
    (a : modal-formula i) →
    is-decidable
      ( (M : type-subtype C) → type-Prop (inclusion-subtype C M ⊨Mₘ a))
  decision-procedure' a =
    is-decidable-Π-is-finite
      ( C-is-fin)
      ( λ (M , M-in-C) →
        ( is-finite-model-valuate-decidable-kripke-models i M
          ( C-sub-fin M M-in-C)
          ( a)))

  decision-procedure : (a : modal-formula i) → bool
  decision-procedure a with decision-procedure' a
  ... | inl _ = true
  ... | inr _ = false

  decision-procedure-correctness :
    {l2 : Level} (theory : modal-theory l2 i) →
    soundness theory C →
    completeness theory C →
    (a : modal-formula i) →
    is-in-subtype theory a ↔ type-prop-bool (decision-procedure a)
  pr1 (decision-procedure-correctness theory sound complete a) in-theory
    with decision-procedure' a
  ... | inl _ = star
  ... | inr not-valid-in-C =
      not-valid-in-C (λ (M , M-in-C) x → sound a in-theory M M-in-C x)
  pr2 (decision-procedure-correctness theory sound complete a) _
    with decision-procedure' a
  ... | inl valid-in-C = complete a (λ M M-in-C → valid-in-C (M , M-in-C))

module _
  {l : Level} {i : Set l}
  where

  is-finite-subformulas-list :
    LEM l →
    (a : modal-formula i) →
    is-finite (type-subtype (subformulas a))
  is-finite-subformulas-list lem a =
    is-finite-is-kuratowsky-finite-set
      ( set-subset (modal-formula-Set i) (subformulas a))
      ( lem)
      ( is-kuratowsky-finite-subformulas-list a)

  is-finite-subtypes-subformulas-list :
    {l2 : Level} →
    LEM (l ⊔ l2) →
    (a : modal-formula i) →
    is-finite (type-subtype (list-subtype (subformulas-list a)) → Prop l2)
  is-finite-subtypes-subformulas-list {l2} lem a =
    is-finite-function-type
      ( is-finite-subformulas-list (lower-LEM l2 lem) a)
      ( is-finite-Prop-LEM (lower-LEM l lem))

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  (lem : LEM l1)
  (lem2 : LEM (l1 ⊔ l2))
  where

  surjection-from-injection :
    type-Set A →
    injection (type-Set A) (type-Set B) →
    type-Set B → type-Set A
  surjection-from-injection a (f , is-inj) b
    with
      lem2
        ( pair
          ( Σ (type-Set A) (λ a → f a ＝ b))
          ( is-prop-all-elements-equal
            ( λ x y →
              ( eq-pair-Σ
                ( is-inj (pr2 x ∙ inv (pr2 y)))
                ( eq-is-prop (is-set-type-Set B _ _))))))
  ... | inl x = pr1 x
  ... | inr x = a

  is-invertible-surjection-from-injection :
    (a0 : type-Set A) →
    (inj@(f , _) : injection (type-Set A) (type-Set B)) →
    (a : type-Set A) →
    surjection-from-injection a0 inj (f a) ＝ a
  is-invertible-surjection-from-injection a0 (f , is-inj) a
    with
      lem2
        ( pair
          ( Σ (type-Set A) (λ a' → f a' ＝ f a))
          ( is-prop-all-elements-equal
            ( λ x y →
              ( eq-pair-Σ
                ( is-inj (pr2 x ∙ inv (pr2 y)))
                ( eq-is-prop (is-set-type-Set B _ _))))))
  ... | inl x = is-inj (pr2 x)
  ... | inr x = ex-falso (x (a , refl))

  is-surjective-surjection-from-injection :
    (a : type-Set A) →
    (inj : injection (type-Set A) (type-Set B)) →
    is-surjective (surjection-from-injection a inj)
  is-surjective-surjection-from-injection a0 (f , is-inj) a =
    unit-trunc-Prop
      ( f a , is-invertible-surjection-from-injection a0 (f , is-inj) a)

  kuratowsky-finite-set-injection :
    injection (type-Set A) (type-Set B) →
    is-kuratowsky-finite-set B →
    is-kuratowsky-finite-set A
  kuratowsky-finite-set-injection inj b-is-fin
    with lem (is-inhabited-Prop (type-Set A))
  ... | inl x =
    apply-twice-universal-property-trunc-Prop
      ( x)
      ( b-is-fin)
      ( is-kuratowsky-finite-set-Prop A)
      ( λ a (n , e) →
        ( unit-trunc-Prop
          ( triple
            ( n)
            ( surjection-from-injection a inj ∘ pr1 e)
            ( is-surjective-comp
              ( is-surjective-surjection-from-injection a inj)
              ( pr2 e)))))
  ... | inr x =
    is-kuratowsky-finite-set-is-finite A
      ( is-finite-is-empty (x ∘ unit-trunc-Prop))

  is-finite-injection :
    injection (type-Set A) (type-Set B) →
    is-finite (type-Set B) →
    is-finite (type-Set A)
  is-finite-injection inj b-is-fin =
    is-finite-is-kuratowsky-finite-set A
      lem (kuratowsky-finite-set-injection inj
        ( is-kuratowsky-finite-set-is-finite B b-is-fin))

module _
  {l1 l2 l3 l4 l5 : Level} (i : Set l3)
  (M : kripke-model l1 l2 i l4)
  (lem : LEM (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5))
  (theory : modal-theory l5 i)
  (is-fin : is-finite (type-subtype theory))
  where

  is-finite-equivalence-classes-filtration :
    is-finite (equivalence-class (Φ-equivalence theory M))
  is-finite-equivalence-classes-filtration =
    is-finite-injection
      ( equivalence-class-Set (Φ-equivalence theory M))
      ( function-Set (type-subtype theory) (Prop-Set (l1 ⊔ l2 ⊔ l4)))
      ( lem)
      ( lem)
      ( injection-map-function-equivalence-class theory M)
      ( is-finite-function-type
        ( is-fin)
        ( is-finite-Prop-LEM
          ( lower-LEM (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5) lem)))

  is-small-equivalence-classes-filtration :
    (l : Level) → is-small l (equivalence-class (Φ-equivalence theory M))
  is-small-equivalence-classes-filtration l =
    is-small-is-finite l
      ( pair
        ( equivalence-class (Φ-equivalence theory M))
        ( is-finite-equivalence-classes-filtration))

module _
  {l1 l2 l3 l4 : Level} (i : Set l3)
  (l5 l6 l7 l8 : Level)
  (lem : LEM (l2 ⊔ lsuc l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6 ⊔ lsuc l7 ⊔ lsuc l8))
  where

  filtration-models-subset-finite-kripke-models :
    filtration-models l1 l2 i l4 l5 l6 l7 l8 ⊆
      finite-kripke-models l1 l2 i l4
  filtration-models-subset-finite-kripke-models M* =
    map-universal-property-trunc-Prop
      ( finite-kripke-models l1 l2 i l4 M*)
      ( λ ((theory , M) , is-fin , is-filt) →
        ( is-finite-equiv
          ( equiv-is-kripke-model-filtration theory M M* is-filt)
          ( is-finite-equivalence-classes-filtration i M
            ( lower-LEM (l2 ⊔ l4) lem)
            ( theory)
            ( is-fin))))

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

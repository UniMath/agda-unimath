# Finite approximability

```agda
module modal-logic.finite-approximability where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.invertible-maps

open import modal-logic.completeness
open import modal-logic.completeness-K
open import modal-logic.formulas
open import modal-logic.kripke-models-filtrations
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.modal-logic-K
open import modal-logic.modal-logic-decision
open import modal-logic.soundness
open import modal-logic.weak-deduction

open import order-theory.maximal-elements-posets

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
    ∃-Prop
      ( model-class l3 l4 i l5 l6)
      ( λ C →
        ( product
          ( soundness logic (finite-subclass i C))
          ( completeness logic (finite-subclass i C))))

  is-finitely-approximable :
    {l2 : Level} (l3 l4 l5 l6 : Level) →
    modal-theory l2 i →
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ lsuc l6)
  is-finitely-approximable l3 l4 l5 l6 logic =
    type-Prop (is-finitely-approximable-Prop l3 l4 l5 l6 logic)

  module _
    (lem : LEM (lsuc (lsuc l1)))
    (zorn : Zorn (lsuc l1) l1 l1)
    (prop-resize : propositional-resizing l1 (lsuc l1))
    where

    K-finite-class :
      model-class (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1) (lsuc (lsuc (lsuc l1)))
    K-finite-class =
      filtrate-class i
        ( all-models (lsuc l1) l1 i l1)
        ( minimal-kripke-model-filtration i)

    K-finite-class-sub-filtration-models :
      K-finite-class ⊆
        filtration-models
          (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1) l1 (lsuc l1) l1 l1
    K-finite-class-sub-filtration-models M* =
      map-universal-property-trunc-Prop
        ( filtration-models _ _ i _ _ _ _ _ M*)
        ( λ ((a , M , _) , p) →
          ( tr (is-in-subtype (filtration-models _ _ i _ _ _ _ _)) (inv p)
            ( intro-∃
              ( in-list (subformulas-list i a) , M)
              ( pair
                (is-finite-subformulas-list
                  ( i)
                  ( lower-LEM (lsuc (lsuc l1)) lem)
                  ( a))
                ( is-kripke-model-filtration-minimal-kripke-model-filtration
                  ( i)
                  ( in-list (subformulas-list i a))
                  ( M)
                  ( is-modal-theory-closed-under-subformulas-subformulas-list
                    ( i)
                    ( a)))))))

    completeness-K-filtration :
      completeness (modal-logic-K i) (K-finite-class)
    completeness-K-filtration =
      filtrate-completeness i
        ( all-models (lsuc l1) l1 i l1)
        ( minimal-kripke-model-filtration i)
        ( λ (M , _) theory theory-is-closed →
          ( is-kripke-model-filtration-minimal-kripke-model-filtration i
            ( theory)
            ( M)
            ( theory-is-closed)))
        ( modal-logic-K i)
        ( completeness-K i (lower-LEM (lsuc (lsuc l1)) lem) zorn prop-resize)

    soundness-K-filtration :
      soundness (modal-logic-K i) (K-finite-class)
    soundness-K-filtration =
      filtrate-soundness i
        ( all-models (lsuc l1) l1 i l1)
        ( minimal-kripke-model-filtration i)
        ( modal-logic-K i)
        ( all-models (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1))
        ( λ _ _ → star)
        ( λ a in-logic M _ x →
          ( soundness-K i a in-logic M (λ b y → lem ((M , y) ⊨ b)) x))

    is-finitely-approximable-K :
      is-finitely-approximable
        ( lsuc (lsuc l1))
        ( lsuc l1)
        ( lsuc l1)
        ( lsuc (lsuc (lsuc l1)))
        ( modal-logic-K i)
    is-finitely-approximable-K =
      intro-∃
        ( K-finite-class)
        ( pair
          ( soundness-subclass
            ( modal-logic-K i)
            ( K-finite-class)
            ( finite-subclass i K-finite-class)
            ( subtype-intersection-right
              ( finite-models (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1))
              ( K-finite-class))
            ( soundness-K-filtration))
          ( transitive-leq-subtype
            ( class-modal-logic (finite-subclass i K-finite-class))
            ( class-modal-logic K-finite-class)
            ( modal-logic-K i)
            ( completeness-K-filtration)
            ( λ a a-in-logic M M-in-class →
              ( a-in-logic M
                ( pair
                  ( transitive-leq-subtype
                    ( K-finite-class)
                    ( filtration-models
                      ( lsuc (lsuc l1))
                      ( lsuc l1)
                      ( i)
                      ( lsuc l1)
                      ( l1)
                      ( lsuc l1)
                      ( l1)
                      ( l1))
                    ( finite-models (lsuc (lsuc l1)) (lsuc l1) i (lsuc l1))
                    ( filtration-models-subset-finite-models i l1
                      (lsuc l1) l1 l1 lem)
                    ( K-finite-class-sub-filtration-models)
                    ( M)
                    ( M-in-class))
                  ( M-in-class))))))
```

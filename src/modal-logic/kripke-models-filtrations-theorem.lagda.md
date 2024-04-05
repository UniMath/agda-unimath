# Kripke models filtrations theorem

```agda
module modal-logic.kripke-models-filtrations-theorem where
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
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.invertible-maps

open import modal-logic.completeness
open import modal-logic.formulas
open import modal-logic.kripke-models-filtrations
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} (i : Set l3)
  (theory : modal-theory l5 i)
  (theory-is-closed : is-modal-theory-closed-under-subformulas i theory)
  (M : kripke-model l1 l2 i l4) (M* : kripke-model l6 l7 i l8)
  where

  kripke-models-filtrations-theorem' :
    (is-filtration : is-kripke-model-filtration-Σ i theory M M*)
    (a : formula i) →
    is-in-subtype theory a →
    (x : type-kripke-model i M) →
    type-iff-Prop
      ( (M , x) ⊨ a)
      ( pair
        ( M*)
        ( map-equiv-is-kripke-model-filtration i theory M M* is-filtration
          ( class (Φ-equivalence i theory M) x))
        ⊨ a)
  pr1 (kripke-models-filtrations-theorem' is-filtration (var n) in-theory x) f =
    map-raise
      ( forward-implication
        ( is-filtration-valuate-is-kripke-model-filtration
          ( i)
          ( theory)
          ( M)
          ( M*)
          ( is-filtration)
          ( n)
          ( x))
      ( in-theory , map-inv-raise f))
  pr1 (kripke-models-filtrations-theorem' is-filtration ⊥ in-theory x) =
    map-raise ∘ map-inv-raise
  pr1 (kripke-models-filtrations-theorem' is-filtration (a →ₘ b) in-theory x)
    fab fa =
      forward-implication
        ( kripke-models-filtrations-theorem' is-filtration b
          ( pr2 (theory-is-closed in-theory))
          ( x))
        ( fab
          ( backward-implication
            ( kripke-models-filtrations-theorem' is-filtration a
              ( pr1 (theory-is-closed in-theory))
              ( x))
            ( fa)))
  pr1 (kripke-models-filtrations-theorem' is-filtration (□ a) in-theory x)
    f y* r-xy =
      apply-universal-property-trunc-Prop
        ( is-inhabited-subtype-equivalence-class
          ( Φ-equivalence i theory M)
          ( map-inv-equiv-is-kripke-model-filtration i theory M M*
            ( is-filtration)
            ( y*)))
        ( (M* , y*) ⊨ a)
        ( λ (y , y-in-class) →
          ( let y*-id-class
                  = concat
                      ( ap
                        ( map-equiv-is-kripke-model-filtration i theory M M*
                          ( is-filtration))
                        ( eq-class-equivalence-class
                          ( Φ-equivalence i theory M)
                          ( map-inv-equiv-is-kripke-model-filtration i theory M
                            ( M*)
                            ( is-filtration)
                            ( y*))
                          ( y-in-class)))
                      ( y*)
                      ( is-retraction-map-retraction-map-equiv
                        ( inv-equiv
                          ( equiv-is-kripke-model-filtration i theory M M*
                            ( is-filtration)))
                        ( y*))
            in tr
                ( λ z* → type-Prop ((M* , z*) ⊨ a))
                ( y*-id-class)
                ( forward-implication
                  ( kripke-models-filtrations-theorem' is-filtration a
                    ( theory-is-closed in-theory)
                    ( y))
                  ( filtration-relation-upper-bound-is-kripke-model-filtration
                    ( i)
                    ( theory)
                    ( M)
                    ( M*)
                    ( is-filtration)
                    ( a)
                    ( in-theory)
                    ( x)
                    ( y)
                    ( tr
                      ( relation-kripke-model i M*
                        ( map-equiv-is-kripke-model-filtration i theory M M*
                          ( is-filtration)
                          ( class (Φ-equivalence i theory M) x)))
                      ( inv y*-id-class)
                      ( r-xy))
                    (f)))))
  pr2 (kripke-models-filtrations-theorem' is-filtration (var n) in-theory x) f =
    map-raise
      ( pr2
        ( backward-implication
          ( is-filtration-valuate-is-kripke-model-filtration i theory M M*
            ( is-filtration)
            ( n)
            ( x))
          ( map-inv-raise f)))
  pr2 (kripke-models-filtrations-theorem' is-filtration ⊥ in-theory x) =
    map-raise ∘ map-inv-raise
  pr2 (kripke-models-filtrations-theorem' is-filtration (a →ₘ b) in-theory x)
    fab fa =
      backward-implication
        ( kripke-models-filtrations-theorem' is-filtration b
          ( pr2 (theory-is-closed in-theory))
          ( x))
        ( fab
          ( forward-implication
            ( kripke-models-filtrations-theorem' is-filtration a
              ( pr1 (theory-is-closed in-theory))
              ( x))
            ( fa)))
  pr2 (kripke-models-filtrations-theorem' is-filtration (□ a) in-theory x)
    f y r-xy =
      backward-implication
        ( kripke-models-filtrations-theorem' is-filtration a
          ( theory-is-closed in-theory)
          ( y))
        ( f
          ( map-equiv-is-kripke-model-filtration i theory M M* is-filtration
            ( class (Φ-equivalence i theory M) y))
          ( filtration-relation-lower-bound-is-kripke-model-filtration i theory
            ( M)
            ( M*)
            ( is-filtration)
            ( x)
            ( y)
            ( r-xy)))
```

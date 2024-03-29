# Canonical threories

```agda
module modal-logic.canonical-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.coproduct-types

open import modal-logic.axioms
open import modal-logic.canonical-model-theorem
open import modal-logic.completeness
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.modal-logic-K
open import modal-logic.modal-logic-S5
open import modal-logic.soundness
open import modal-logic.weak-deduction

open import order-theory.maximal-elements-posets
```

</details>

## Idea

TODO

## Definition

```agda
-- TODO: levels
module _
  {l1 : Level}
  (i : Set l1)
  (lem : LEM l1)
  (zorn : Zorn (lsuc l1) l1 l1)
  (prop-resize : propositional-resizing l1 (lsuc l1))
  (axioms : modal-theory l1 i)
  (is-cons : is-consistent-modal-logic (modal-logic axioms))
  (contains-K : modal-logic-K i ⊆ modal-logic axioms)
  where

  is-canonical-ax-m :
    ax-m i ⊆ modal-logic axioms →
    is-in-subtype
      ( reflexive-kripke-class (lsuc l1) l1 i l1)
      ( canonical-kripke-model axioms zorn prop-resize is-cons contains-K)
  is-canonical-ax-m ax-m-subset x a box-a-in-x =
    weak-modal-logic-subset-complete-theory
      ( axioms)
      ( zorn)
      ( prop-resize)
      ( is-cons)
      ( contains-K)
      ( pr1 x , pr1 (pr2 x))
      ( pr2 (pr2 x))
      ( a)
      ( weak-modal-logic-mp
        ( weak-modal-logic-ax
          ( logic-subset-L-complete-theory
            ( axioms)
            ( zorn)
            ( prop-resize)
            ( is-cons)
            ( contains-K)
            ( pr1 x , pr1 (pr2 x))
            ( pr2 (pr2 x))
            ( □ a →ₘ a)
            ( ax-m-subset _ (a , refl))))
        ( weak-modal-logic-ax box-a-in-x))

  is-canonical-ax-b :
    ax-b i ⊆ modal-logic axioms →
    is-in-subtype
      ( symmetry-kripke-class (lsuc l1) l1 i l1)
      ( canonical-kripke-model axioms zorn prop-resize is-cons contains-K)
  is-canonical-ax-b ax-b-subset x y r-xy a box-a-in-y =
      lemma-box-diamond
        ( axioms)
        ( zorn)
        ( prop-resize)
        ( is-cons)
        ( contains-K)
        ( lem)
        ( pr1 y , pr1 (pr2 y))
        ( pr2 (pr2 y))
        ( pr1 x , pr1 (pr2 x))
        ( pr2 (pr2 x))
        ( λ b →
          ( map-universal-property-trunc-Prop
            ( pr1 y b)
            ( λ { (c , refl , c-in-x) →
              ( r-xy (◇ c)
                ( weak-modal-logic-subset-complete-theory
                  ( axioms)
                  ( zorn)
                  ( prop-resize)
                  ( is-cons)
                  ( contains-K)
                  ( pr1 x , pr1 (pr2 x))
                  ( pr2 (pr2 x))
                  ( □ ◇ c)
                  ( weak-modal-logic-mp
                    ( weak-modal-logic-ax
                      ( logic-subset-L-complete-theory
                        ( axioms)
                        ( zorn)
                        ( prop-resize)
                        ( is-cons)
                        ( contains-K)
                        ( pr1 x , pr1 (pr2 x))
                        ( pr2 (pr2 x))
                        ( c →ₘ □ ◇ c)
                        ( ax-b-subset _ (c , refl))))
                    ( weak-modal-logic-ax c-in-x))))})))
        ( a)
        ( box-a-in-y)

  is-canonical-ax-4 :
    ax-4 i ⊆ modal-logic axioms →
    is-in-subtype
      ( transitivity-kripke-class (lsuc l1) l1 i l1)
      ( canonical-kripke-model axioms zorn prop-resize is-cons contains-K)
  is-canonical-ax-4 ax-4-subset x y z r-yz r-xy a box-a-in-x =
      r-yz a
        ( r-xy (□ a)
          ( weak-modal-logic-subset-complete-theory
          ( axioms)
          ( zorn)
          ( prop-resize)
          ( is-cons)
          ( contains-K)
          ( pr1 x , pr1 (pr2 x))
          ( pr2 (pr2 x))
          ( □ □ a)
          ( weak-modal-logic-mp
            ( weak-modal-logic-ax
              ( logic-subset-L-complete-theory
                ( axioms)
                ( zorn)
                ( prop-resize)
                ( is-cons)
                ( contains-K)
                ( pr1 x , pr1 (pr2 x))
                ( pr2 (pr2 x))
                ( □ a →ₘ □ □ a)
                ( ax-4-subset _ (a , refl))))
            ( weak-modal-logic-ax box-a-in-x))))
```

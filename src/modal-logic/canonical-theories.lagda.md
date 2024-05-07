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
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.l-complete-theories
open import modal-logic.modal-logic-k
open import modal-logic.modal-logic-s5
open import modal-logic.soundness
open import modal-logic.weak-deduction

open import order-theory.zorn
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 : Level}
  (i : Set l1)
  (zorn : Zorn (lsuc l1) l1 l1)
  (prop-resize : propositional-resizing l1 (lsuc l1))
  (logic : modal-theory l1 i)
  (is-logic : is-modal-logic logic)
  (is-cons : is-consistent-modal-logic logic)
  (is-normal : is-normal-modal-logic logic)
  where

  private
    contains-ax-k : ax-k i ⊆ logic
    contains-ax-k =
      transitive-leq-subtype
        ( ax-k i)
        ( modal-logic-K i)
        ( logic)
        ( is-normal)
        ( K-contains-ax-k i)

    contains-ax-s : ax-s i ⊆ logic
    contains-ax-s =
      transitive-leq-subtype
        ( ax-s i)
        ( modal-logic-K i)
        ( logic)
        ( is-normal)
        ( K-contains-ax-s i)

    contains-ax-dn : ax-dn i ⊆ logic
    contains-ax-dn =
      transitive-leq-subtype
        ( ax-dn i)
        ( modal-logic-K i)
        ( logic)
        ( is-normal)
        ( K-contains-ax-dn i)

  is-canonical-ax-m :
    ax-m i ⊆ logic →
    is-in-subtype
      ( reflexive-kripke-class (lsuc l1) l1 i l1)
      ( canonical-kripke-model
        ( logic)
        ( is-logic)
        ( is-cons)
        ( is-normal)
        ( zorn)
        ( prop-resize))
  is-canonical-ax-m ax-m-subset x a box-a-in-x =
    weak-modal-logic-mp
      ( is-weak-modal-logic-L-complete-theory logic lzero x)
      ( subset-logic-L-complete-theory logic lzero x
        ( □ₘ a →ₘ a)
        ( ax-m-subset (□ₘ a →ₘ a) (a , refl)))
      ( box-a-in-x)

  is-canonical-ax-b :
    LEM l1 →
    ax-b i ⊆ logic →
    is-in-subtype
      ( symmetry-kripke-class (lsuc l1) l1 i l1)
      ( canonical-kripke-model
        ( logic)
        ( is-logic)
        ( is-cons)
        ( is-normal)
        ( zorn)
        ( prop-resize))
  is-canonical-ax-b lem ax-b-subset x y xRy a box-a-in-y =
    lemma-box-diamond-L-complete logic x
      ( contains-ax-k)
      ( contains-ax-s)
      ( contains-ax-dn)
      ( lem)
      ( is-logic)
      ( is-normal)
      ( y)
      ( λ b →
        ( map-universal-property-trunc-Prop
          ( modal-theory-L-complete-theory logic y b)
          ( λ { (c , c-in-x , refl) →
            ( xRy (◇ₘ c)
              ( weak-modal-logic-mp
                ( is-weak-modal-logic-L-complete-theory logic lzero x)
                ( subset-logic-L-complete-theory logic lzero x (c →ₘ □ₘ ◇ₘ c)
                  ( ax-b-subset (c →ₘ □ₘ ◇ₘ c) (c , refl)))
                ( c-in-x)))})))
      ( a)
      ( box-a-in-y)

  is-canonical-ax-4 :
    ax-4 i ⊆ logic →
    is-in-subtype
      ( transitivity-kripke-class (lsuc l1) l1 i l1)
      ( canonical-kripke-model
        ( logic)
        ( is-logic)
        ( is-cons)
        ( is-normal)
        ( zorn)
        ( prop-resize))
  is-canonical-ax-4 ax-4-subset x y z yRz xRy a box-a-in-x =
    yRz a
      ( xRy (□ₘ a)
        ( weak-modal-logic-mp
          ( is-weak-modal-logic-L-complete-theory logic lzero x)
          ( subset-logic-L-complete-theory logic lzero x
            ( □ₘ a →ₘ □ₘ □ₘ a)
            ( ax-4-subset (□ₘ a →ₘ □ₘ □ₘ a) (a , refl)))
          ( box-a-in-x)))
```

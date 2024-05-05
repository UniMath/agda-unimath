# Completeness of S5

```agda
module modal-logic.completeness-s5 where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negation
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

open import modal-logic.axioms
open import modal-logic.canonical-model-theorem
open import modal-logic.canonical-theories
open import modal-logic.completeness
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
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
  (lem : LEM l1)
  (zorn : Zorn-non-empty (lsuc l1) l1 l1)
  (prop-resize : propositional-resizing l1 (lsuc l1))
  where

  S5-canonical-model-is-equivalence :
    is-in-subtype
      ( equivalence-kripke-class (lsuc l1) l1 i l1)
      ( canonical-kripke-model
        ( modal-logic-S5 i)
        ( is-modal-logic-S5 i)
        ( is-consistent-S5 i)
        ( is-normal-modal-logic-S5 i)
        ( lem)
        ( zorn)
        ( prop-resize))
  S5-canonical-model-is-equivalence =
    triple
      ( is-canonical-ax-m i lem zorn prop-resize
        ( modal-logic-S5 i)
        ( is-modal-logic-S5 i)
        ( is-consistent-S5 i)
        ( is-normal-modal-logic-S5 i)
        ( modal-logic-S5-contains-ax-m i))
      ( is-canonical-ax-b i lem zorn prop-resize
        ( modal-logic-S5 i)
        ( is-modal-logic-S5 i)
        ( is-consistent-S5 i)
        ( is-normal-modal-logic-S5 i)
        ( modal-logic-S5-contains-ax-b i))
      ( is-canonical-ax-4 i lem zorn prop-resize
        ( modal-logic-S5 i)
        ( is-modal-logic-S5 i)
        ( is-consistent-S5 i)
        ( is-normal-modal-logic-S5 i)
        ( modal-logic-S5-contains-ax-4 i))

  completeness-S5 :
    completeness (modal-logic-S5 i) (equivalence-kripke-class (lsuc l1) l1 i l1)
  completeness-S5 =
    canonical-model-completness
      ( modal-logic-S5 i)
      ( is-modal-logic-S5 i)
      ( is-consistent-S5 i)
      ( is-normal-modal-logic-S5 i)
      ( lem)
      ( zorn)
      ( prop-resize)
      ( equivalence-kripke-class (lsuc l1) l1 i l1)
      ( S5-canonical-model-is-equivalence)
```

# Completeness of K

```agda
module modal-logic.completeness-K where
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
open import modal-logic.completeness
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.modal-logic-K
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
  where

  completeness-K : completeness (modal-logic-K i) (all-models (lsuc l1) l1 i l1)
  completeness-K =
    canonical-model-completness
      ( modal-logic-K-axioms i)
      ( zorn)
      ( prop-resize)
      ( is-consistent-K i)
      ( refl-leq-subtype (modal-logic-K i))
      ( lem)
      ( all-models (lsuc l1) l1 i l1)
      ( star)
```

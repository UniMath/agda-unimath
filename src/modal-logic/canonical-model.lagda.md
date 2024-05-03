# Canonical model theorem

```agda
module modal-logic.canonical-model where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.subtypes

open import modal-logic.axioms
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.l-complete-theories
open import modal-logic.l-consistent-theories
open import modal-logic.weak-deduction

open import order-theory.zorn
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} {i : Set l1}
  (logic : modal-theory l2 i)
  (is-logic : is-weak-modal-logic logic)
  (is-cons : is-consistent-modal-logic logic)
  (contains-ax-k : ax-k i ⊆ logic)
  (contains-ax-s : ax-s i ⊆ logic)
  (zorn : Zorn-non-empty (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2) l2)
  (prop-resize : propositional-resizing (l1 ⊔ l2) (lsuc (l1 ⊔ l2)))
  where

  canonical-kripke-model :
    kripke-model (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2) i (l1 ⊔ l2)
  pr1 (pr1 (pr1 canonical-kripke-model)) =
    L-complete-theory logic (l1 ⊔ l2)
  pr2 (pr1 (pr1 canonical-kripke-model)) =
    is-inhabited-L-complete-theory
      ( logic)
      ( prop-resize)
      ( zorn)
      ( is-logic)
      ( is-cons)
      ( contains-ax-k)
      ( contains-ax-s)
  pr2 (pr1 canonical-kripke-model) x y =
    Π-Prop
      ( formula i)
      ( λ a →
        ( hom-Prop
          ( modal-theory-L-complete-theory logic x (□ a))
          ( modal-theory-L-complete-theory logic y a)))
  pr2 canonical-kripke-model n x =
    modal-theory-L-complete-theory logic x (var n)
```

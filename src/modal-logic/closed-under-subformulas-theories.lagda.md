# Closed under subformulas theories

```agda
module modal-logic.closed-under-subformulas-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.transitive-closures-binary-relations
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.injective-maps
open import foundation-core.transport-along-identifications

open import modal-logic.axioms
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.kripke-semantics

open import univalent-combinatorics.finite-types
```

</details>

## Idea

Theory is closed under subformulas if every subformula of a formula in the
theory is also in the theory.

## Definition

```agda
module _
  {l1 l2 : Level} {i : Set l1} (theory : modal-theory l2 i)
  where

  is-modal-theory-has-subboxes-Prop : Prop (l1 ⊔ l2)
  is-modal-theory-has-subboxes-Prop =
    implicit-Π-Prop (modal-formula i) (λ a → theory (□ₘ a) ⇒ theory a)

  is-modal-theory-has-subboxes : UU (l1 ⊔ l2)
  is-modal-theory-has-subboxes = type-Prop is-modal-theory-has-subboxes-Prop

  is-modal-theory-has-subimps-Prop : Prop (l1 ⊔ l2)
  is-modal-theory-has-subimps-Prop =
    implicit-Π-Prop (modal-formula i × modal-formula i)
      ( λ (a , b) → theory (a →ₘ b) ⇒ product-Prop (theory a) (theory b))

  is-modal-theory-has-subimps : UU (l1 ⊔ l2)
  is-modal-theory-has-subimps = type-Prop is-modal-theory-has-subimps-Prop

  is-modal-theory-closed-under-subformulas-Prop : Prop (l1 ⊔ l2)
  is-modal-theory-closed-under-subformulas-Prop =
    product-Prop
      ( is-modal-theory-has-subboxes-Prop)
      ( is-modal-theory-has-subimps-Prop)

  is-modal-theory-closed-under-subformulas : UU (l1 ⊔ l2)
  is-modal-theory-closed-under-subformulas =
    type-Prop is-modal-theory-closed-under-subformulas-Prop

  is-has-subboxes-is-closed-under-subformulas :
    is-modal-theory-closed-under-subformulas → is-modal-theory-has-subboxes
  is-has-subboxes-is-closed-under-subformulas = pr1

  is-has-subimps-is-closed-under-subformulas :
    is-modal-theory-closed-under-subformulas → is-modal-theory-has-subimps
  is-has-subimps-is-closed-under-subformulas = pr2
```

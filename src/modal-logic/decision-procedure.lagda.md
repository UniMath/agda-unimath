# Modal logic decision

```agda
module modal-logic.decision-procedure where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import modal-logic.completeness
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.soundness

open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.finite-types
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
```

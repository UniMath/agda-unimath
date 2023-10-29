# Modal logic completeness

```agda
module modal-logic.completeness where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.coproduct-types

open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {i : Set l1} (logic : formulas l2 i)
  {w : UU l3} (C : model-class w l4 i l5 l6)
  where

  completeness : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ l6)
  completeness = class-modal-logic C ⊆ logic
```

## Properties

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {i : Set l1} (logic : formulas l2 i)
  {w : UU l3}
  (C₁ : model-class w l4 i l5 l6) (C₂ : model-class w l4 i l5 l7)
  where

  completeness-subclass :
    C₁ ⊆ C₂ → completeness logic C₁ → completeness logic C₂
  completeness-subclass sub complete =
    transitive-leq-subtype
      ( class-modal-logic C₂)
      ( class-modal-logic C₁)
      ( logic)
      ( complete)
      ( class-modal-logic-monotic C₁ C₂ sub)
```

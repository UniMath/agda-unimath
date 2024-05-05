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
  {l1 l2 l3 l4 l5 l6 : Level} {i : Set l1}
  where

  completeness :
    modal-theory l2 i →
    model-class l3 l4 i l5 l6 →
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ l6)
  completeness logic C = class-modal-logic C ⊆ logic
```

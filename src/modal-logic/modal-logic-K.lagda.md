# Modal logic K

```agda
module modal-logic.modal-logic-K where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.sets
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import modal-logic.axioms
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.modal-logic-IK
open import modal-logic.soundness
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l : Level} (i : Set l)
  where

  modal-logic-K : formulas l i
  modal-logic-K = modal-logic (union-subtype (modal-logic-IK i) (ax-dn i))

  IK-subset-K : modal-logic-IK i ⊆ modal-logic-K
  IK-subset-K =
    transitive-leq-subtype
      ( modal-logic-IK i)
      ( union-subtype (modal-logic-IK i) (ax-dn i))
      ( modal-logic-K)
      ( axioms-subset-modal-logic _)
      ( subtype-union-left (modal-logic-IK i) (ax-dn i))

module _
  {l1 l2 l3 : Level}
  (i : Set l1) (axioms : formulas l2 i)
  (w : UU l3)
  {l4 l5 : Level}
  where

  soundness-K : soundness (modal-logic-K i) (decidable-models w l4 i l5)
  soundness-K =
    soundness-modal-logic-union-subclass-right-sublevels
      ( modal-logic-IK i)
      ( ax-dn i)
      ( l1 ⊔ l3 ⊔ l4 ⊔ l5)
      ( all-models w l4 i l5)
      ( decidable-models w l4 i l5)
      ( soundness-IK i w l4 l5)
      ( ax-dn-soundness i w l4 l5)
      ( all-models-is-largest-class w l4 i l5 (decidable-models w l4 i l5))

  soundness-K-finite : soundness (modal-logic-K i) (finite-models w l4 i l5)
  soundness-K-finite =
    soundness-subclass
      ( modal-logic-K i)
      ( decidable-models w l4 i l5)
      ( finite-models w l4 i l5)
      ( finite-models-subclass-decidable-models w l4 i l5)
      ( soundness-K)
```

# Modal logic K

```agda
module modal-logic.modal-logic-K where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.sets
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

module _
  {l1 l2 l3 : Level}
  (i : Set l1) (axioms : formulas l2 i)
  (w : Inhabited-Type l3)
  {l4 l5 : Level}
  where

  -- soundness-K : soundness (modal-logic-K i) (decidable-models w l4 i l5)
  -- soundness-K =
  --   {!  !}
```

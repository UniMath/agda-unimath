# Modal logic IK

```agda
module modal-logic.modal-logic-IK where
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

-- TODO: It's not Intuitionistic K
  modal-logic-IK : formulas l i
  modal-logic-IK =
    modal-logic (union-subtype (ax-k i) (union-subtype (ax-s i) (ax-n i)))

module _
  {l1 l2 : Level}
  (i : Set l1)
  (w : UU l2)
  (l3 l4 : Level)
  where

  soundness-IK : soundness (modal-logic-IK i) (all-models w l3 i l4)
  soundness-IK =
    soundness-modal-logic-union-same-class
      ( ax-k i)
      ( union-subtype (ax-s i) (ax-n i))
      ( all-models w l3 i l4)
      ( ax-k-soundness i w l3 l4)
      ( soundness-union-same-class
        ( ax-s i)
        ( ax-n i)
        ( all-models w l3 i l4)
        ( ax-s-soundness i w l3 l4)
        ( ax-n-soundness i w l3 l4))
```

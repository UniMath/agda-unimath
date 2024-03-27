# Modal logic S5

```agda
module modal-logic.modal-logic-S5 where
```

<details><summary>Imports</summary>

```agda
open import foundation.intersections-subtypes
open import foundation.sets
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.coproduct-types

open import modal-logic.axioms
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.modal-logic-K
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

  modal-logic-S5-axioms : formulas l i
  modal-logic-S5-axioms = modal-logic-K-axioms i ∪ (ax-m i ∪ (ax-b i ∪ ax-4 i))

  modal-logic-S5 : formulas l i
  modal-logic-S5 = modal-logic modal-logic-S5-axioms

  modal-logic-K-sub-S5 : modal-logic-K i ⊆ modal-logic-S5
  modal-logic-K-sub-S5 =
    modal-logic-monotic
      ( subtype-union-left
        ( modal-logic-K-axioms i)
        ( ax-m i ∪ (ax-b i ∪ ax-4 i)))

module _
  {l1 l2 l3 l4 : Level} (i : Set l1)
  where

  soundness-S5-additional-axioms :
    soundness (ax-m i ∪ (ax-b i ∪ ax-4 i)) (equivalence-class l2 l3 i l4)
  soundness-S5-additional-axioms =
    soundness-union
      ( ax-m i)
      ( ax-b i ∪ ax-4 i)
      ( reflexive-class l2 l3 i l4)
      ( intersection-subtype
        ( symmetry-class l2 l3 i l4)
        ( transitivity-class l2 l3 i l4))
      ( ax-m-soundness i l3 l4)
      ( soundness-union
        ( ax-b i)
        ( ax-4 i)
        ( symmetry-class l2 l3 i l4)
        ( transitivity-class l2 l3 i l4)
        ( ax-b-soundness i l3 l4)
        ( ax-4-soundness i l3 l4))

  soundness-S5-axioms :
    soundness
      ( modal-logic-S5-axioms i)
      ( decidable-subclass i (equivalence-class l2 l3 i l4))
  soundness-S5-axioms =
    soundness-union
      ( modal-logic-K-axioms i)
      ( ax-m i ∪ (ax-b i ∪ ax-4 i))
      ( decidable-models l2 l3 i l4)
      ( equivalence-class l2 l3 i l4)
      ( soundness-K-axioms i)
      ( soundness-S5-additional-axioms)

  soundness-S5 :
    soundness
      ( modal-logic-S5 i)
      ( decidable-subclass i (equivalence-class l2 l3 i l4))
  soundness-S5 =
    soundness-modal-logic
      ( decidable-subclass i (equivalence-class l2 l3 i l4))
      ( soundness-S5-axioms)
```

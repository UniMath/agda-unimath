# Modal logic K

```agda
module modal-logic.modal-logic-K where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types

open import modal-logic.axioms
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.modal-logic-IK
open import modal-logic.soundness

open import univalent-combinatorics.finite-types
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
  modal-logic-K =
    modal-logic (union-subtype (modal-logic-IK i) (ax-dn i))

  IK-subset-K : modal-logic-IK i ⊆ modal-logic-K
  IK-subset-K =
    transitive-leq-subtype
      ( modal-logic-IK i)
      ( union-subtype (modal-logic-IK i) (ax-dn i))
      ( modal-logic-K)
      ( axioms-subset-modal-logic _)
      ( subtype-union-left (modal-logic-IK i) (ax-dn i))

  K-contains-ax-k : ax-k i ⊆ modal-logic-K
  K-contains-ax-k =
    transitive-leq-subtype
      ( ax-k i)
      ( modal-logic-IK i)
      ( modal-logic-K)
      ( IK-subset-K)
      ( IK-contains-ax-k i)

  K-contains-ax-s : ax-s i ⊆ modal-logic-K
  K-contains-ax-s =
    transitive-leq-subtype
      ( ax-s i)
      ( modal-logic-IK i)
      ( modal-logic-K)
      ( IK-subset-K)
      ( IK-contains-ax-s i)

  K-contains-ax-n : ax-n i ⊆ modal-logic-K
  K-contains-ax-n =
    transitive-leq-subtype
      ( ax-n i)
      ( modal-logic-IK i)
      ( modal-logic-K)
      ( IK-subset-K)
      ( IK-contains-ax-n i)

  K-contains-ax-dn : ax-dn i ⊆ modal-logic-K
  K-contains-ax-dn =
    transitive-leq-subtype
      ( ax-dn i)
      ( union-subtype (modal-logic-IK i) (ax-dn i))
      ( modal-logic (union-subtype (modal-logic-IK i) (ax-dn i)))
      ( axioms-subset-modal-logic
        ( union-subtype (modal-logic-IK i) (ax-dn i)))
      ( subtype-union-right (modal-logic-IK i) (ax-dn i))

module _
  {l1 l2 l3 l4 : Level}
  (i : Set l1) (w : UU l2)
  where

  soundness-K : soundness (modal-logic-K i) (decidable-models w l3 i l4)
  soundness-K =
    soundness-modal-logic-union-subclass-right-sublevels
      ( modal-logic-IK i)
      ( ax-dn i)
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4)
      ( all-models w l3 i l4)
      ( decidable-models w l3 i l4)
      ( soundness-IK i w l3 l4)
      ( ax-dn-soundness i w l3 l4)
      ( all-models-is-largest-class w l3 i l4 (decidable-models w l3 i l4))

  soundness-K-finite : soundness (modal-logic-K i) (finite-models w l3 i l4)
  soundness-K-finite =
    soundness-subclass
      ( modal-logic-K i)
      ( decidable-models w l3 i l4)
      ( finite-models w l3 i l4)
      ( finite-models-subclass-decidable-models w l3 i l4)
      ( soundness-K)

module _
  {l1 : Level} (i : Set l1)
  where

  is-consistent-K : is-consistent-modal-logic (modal-logic-K i)
  is-consistent-K bot-in-logic =
    map-inv-raise
      ( soundness-K-finite
        ( i)
        ( unit)
        ( ⊥)
        ( bot-in-logic)
        ( pair
          ( (unit-trunc-Prop star) , (λ _ _ → empty-Prop))
          ( λ _ _ → empty-Prop))
        ( triple
          ( is-finite-unit)
          ( λ _ _ → inr (λ r → r))
          ( λ _ _ → is-decidable-empty))
        ( star))
```

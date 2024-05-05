# Modal logic K

```agda
module modal-logic.modal-logic-k where
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

  -- TODO: refactor
  modal-logic-K-axioms : modal-theory l i
  modal-logic-K-axioms = ((ax-k i ∪ ax-s i) ∪ ax-n i) ∪ ax-dn i

  modal-logic-K : modal-theory l i
  modal-logic-K = modal-logic-closure modal-logic-K-axioms

  is-modal-logic-K : is-modal-logic modal-logic-K
  is-modal-logic-K = subset-double-modal-logic modal-logic-K-axioms

  K-axioms-contains-ax-k : ax-k i ⊆ modal-logic-K-axioms
  K-axioms-contains-ax-k =
    transitive-leq-subtype
      ( ax-k i)
      ( ax-k i ∪ ax-s i)
      ( modal-logic-K-axioms)
      ( transitive-leq-subtype
        ( ax-k i ∪ ax-s i)
        ( (ax-k i ∪ ax-s i) ∪ ax-n i)
        ( modal-logic-K-axioms)
        ( subtype-union-left ((ax-k i ∪ ax-s i) ∪ ax-n i) (ax-dn i))
        ( subtype-union-left (ax-k i ∪ ax-s i) (ax-n i)))
      ( subtype-union-left (ax-k i) (ax-s i))

  K-axioms-contains-ax-s : ax-s i ⊆ modal-logic-K-axioms
  K-axioms-contains-ax-s =
    transitive-leq-subtype
      ( ax-s i)
      ( ax-k i ∪ ax-s i)
      ( modal-logic-K-axioms)
      ( transitive-leq-subtype
        ( ax-k i ∪ ax-s i)
        ( (ax-k i ∪ ax-s i) ∪ ax-n i)
        ( modal-logic-K-axioms)
        ( subtype-union-left ((ax-k i ∪ ax-s i) ∪ ax-n i) (ax-dn i))
        ( subtype-union-left (ax-k i ∪ ax-s i) (ax-n i)))
      ( subtype-union-right (ax-k i) (ax-s i))

  K-axioms-contains-ax-n : ax-n i ⊆ modal-logic-K-axioms
  K-axioms-contains-ax-n =
    transitive-leq-subtype
      ( ax-n i)
      ( (ax-k i ∪ ax-s i) ∪ ax-n i)
      ( modal-logic-K-axioms)
      ( subtype-union-left ((ax-k i ∪ ax-s i) ∪ ax-n i) (ax-dn i))
      ( subtype-union-right (ax-k i ∪ ax-s i) (ax-n i))

  K-axioms-contains-ax-dn : ax-dn i ⊆ modal-logic-K-axioms
  K-axioms-contains-ax-dn =
    subtype-union-right ((ax-k i ∪ ax-s i) ∪ ax-n i) (ax-dn i)

  K-contains-ax-k : ax-k i ⊆ modal-logic-K
  K-contains-ax-k =
    transitive-leq-subtype
      ( ax-k i)
      ( modal-logic-K-axioms)
      ( modal-logic-K)
      ( axioms-subset-modal-logic modal-logic-K-axioms)
      ( K-axioms-contains-ax-k)

  K-contains-ax-s : ax-s i ⊆ modal-logic-K
  K-contains-ax-s =
    transitive-leq-subtype
      ( ax-s i)
      ( modal-logic-K-axioms)
      ( modal-logic-K)
      ( axioms-subset-modal-logic modal-logic-K-axioms)
      ( K-axioms-contains-ax-s)

  K-contains-ax-n : ax-n i ⊆ modal-logic-K
  K-contains-ax-n =
    transitive-leq-subtype
      ( ax-n i)
      ( modal-logic-K-axioms)
      ( modal-logic-K)
      ( axioms-subset-modal-logic modal-logic-K-axioms)
      ( K-axioms-contains-ax-n)

  K-contains-ax-dn : ax-dn i ⊆ modal-logic-K
  K-contains-ax-dn =
    transitive-leq-subtype
      ( ax-dn i)
      ( modal-logic-K-axioms)
      ( modal-logic-K)
      ( axioms-subset-modal-logic modal-logic-K-axioms)
      ( K-axioms-contains-ax-dn)

is-normal-modal-logic :
  {l1 l2 : Level} {i : Set l1} → modal-theory l2 i → UU (l1 ⊔ l2)
is-normal-modal-logic {i = i} logic = modal-logic-K i ⊆ logic

is-normal-modal-logic-K :
  {l1 : Level} (i : Set l1) → is-normal-modal-logic (modal-logic-K i)
is-normal-modal-logic-K i = refl-leq-subtype (modal-logic-K i)

module _
  {l1 l2 l3 l4 : Level} (i : Set l1)
  where

  soundness-K-axioms :
    soundness (modal-logic-K-axioms i) (decidable-models l2 l3 i l4)
  soundness-K-axioms =
    soundness-union-subclass-right-sublevels
      ( (ax-k i ∪ ax-s i) ∪ ax-n i)
      ( ax-dn i)
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4)
      ( all-models l2 l3 i l4)
      ( decidable-models l2 l3 i l4)
      ( soundness-union-same-class
        ( ax-k i ∪ ax-s i)
        ( ax-n i)
        ( all-models l2 l3 i l4)
        ( soundness-union-same-class
          ( ax-k i)
          ( ax-s i)
          ( all-models l2 l3 i l4)
          ( ax-k-soundness i l3 l4)
          ( ax-s-soundness i l3 l4))
        ( ax-n-soundness i l3 l4))
      ( ax-dn-soundness i l3 l4)
      ( all-models-is-largest-class i (decidable-models l2 l3 i l4))

  soundness-K : soundness (modal-logic-K i) (decidable-models l2 l3 i l4)
  soundness-K =
    soundness-modal-logic (decidable-models l2 l3 i l4) soundness-K-axioms

  soundness-K-finite : soundness (modal-logic-K i) (finite-models l2 l3 i l4)
  soundness-K-finite =
    soundness-subclass
      ( modal-logic-K i)
      ( decidable-models l2 l3 i l4)
      ( finite-models l2 l3 i l4)
      ( finite-models-subclass-decidable-models i)
      ( soundness-K)

module _
  {l1 : Level} (i : Set l1)
  where

  is-consistent-K : is-consistent-modal-logic (modal-logic-K i)
  is-consistent-K bot-in-logic =
    map-inv-raise
      ( soundness-K-finite
        ( i)
        ( ⊥)
        ( bot-in-logic)
        ( pair
          ( pair (unit , unit-trunc-Prop star) (λ _ _ → empty-Prop))
          ( λ _ _ → empty-Prop))
        ( triple
          ( is-finite-unit)
          ( λ _ _ → inr (λ r → r))
          ( λ _ _ → is-decidable-empty))
        ( star))
```

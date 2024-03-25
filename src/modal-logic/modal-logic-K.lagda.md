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

  modal-logic-K-axioms : formulas l i
  modal-logic-K-axioms = ax-k i ∪ ax-s i ∪ ax-n i ∪ ax-dn i

  modal-logic-K : formulas l i
  modal-logic-K = modal-logic modal-logic-K-axioms

  K-axioms-contains-ax-k : ax-k i ⊆ modal-logic-K-axioms
  K-axioms-contains-ax-k =
    transitive-leq-subtype
      ( ax-k i)
      ( ax-k i ∪ ax-s i)
      ( modal-logic-K-axioms)
      ( transitive-leq-subtype
        ( ax-k i ∪ ax-s i)
        ( ax-k i ∪ ax-s i ∪ ax-n i)
        ( modal-logic-K-axioms)
        ( subtype-union-left (ax-k i ∪ ax-s i ∪ ax-n i) (ax-dn i))
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
        ( ax-k i ∪ ax-s i ∪ ax-n i)
        ( modal-logic-K-axioms)
        ( subtype-union-left (ax-k i ∪ ax-s i ∪ ax-n i) (ax-dn i))
        ( subtype-union-left (ax-k i ∪ ax-s i) (ax-n i)))
      ( subtype-union-right (ax-k i) (ax-s i))

  K-axioms-contains-ax-n : ax-n i ⊆ modal-logic-K-axioms
  K-axioms-contains-ax-n =
    transitive-leq-subtype
      ( ax-n i)
      ( ax-k i ∪ ax-s i ∪ ax-n i)
      ( modal-logic-K-axioms)
      ( subtype-union-left (ax-k i ∪ ax-s i ∪ ax-n i) (ax-dn i))
      ( subtype-union-right (ax-k i ∪ ax-s i) (ax-n i))

  K-axioms-contains-ax-dn : ax-dn i ⊆ modal-logic-K-axioms
  K-axioms-contains-ax-dn =
    subtype-union-right (ax-k i ∪ ax-s i ∪ ax-n i) (ax-dn i)

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

module _
  {l1 l2 l3 l4 : Level} (i : Set l1)
  where

  soundness-K : soundness (modal-logic-K i) (decidable-models l2 l3 i l4)
  soundness-K =
    soundness-modal-logic-union-subclass-right-sublevels
      ( ax-k i ∪ ax-s i ∪ ax-n i)
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
      ( all-models-is-largest-class l2 l3 i l4 (decidable-models l2 l3 i l4))

  soundness-K-finite : soundness (modal-logic-K i) (finite-models l2 l3 i l4)
  soundness-K-finite =
    soundness-subclass
      ( modal-logic-K i)
      ( decidable-models l2 l3 i l4)
      ( finite-models l2 l3 i l4)
      ( finite-models-subclass-decidable-models l2 l3 i l4)
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
        ( unit)
        ( pair
          ( pair (unit-trunc-Prop star) (λ _ _ → empty-Prop))
          ( λ _ _ → empty-Prop))
        ( triple
          ( is-finite-unit)
          ( λ _ _ → inr (λ r → r))
          ( λ _ _ → is-decidable-empty))
        ( star))
```

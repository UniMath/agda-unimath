# Modal logic S5

```agda
module modal-logic.modal-logic-s5 where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.intersections-subtypes
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
open import modal-logic.modal-logic-k
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

  modal-logic-S5-axioms : modal-theory l i
  modal-logic-S5-axioms = modal-logic-K-axioms i ∪ ax-m i ∪ ax-b i ∪ ax-4 i

  modal-logic-S5 : modal-theory l i
  modal-logic-S5 = modal-logic-closure modal-logic-S5-axioms

  is-modal-logic-S5 : is-modal-logic modal-logic-S5
  is-modal-logic-S5 = subset-double-modal-logic modal-logic-S5-axioms

  is-normal-modal-logic-S5 : is-normal-modal-logic modal-logic-S5
  is-normal-modal-logic-S5 =
    modal-logic-monotic
      ( subtype-union-left
        ( modal-logic-K-axioms i)
        ( ax-m i ∪ (ax-b i ∪ ax-4 i)))

  modal-logic-S5-axioms-contains-ax-m : ax-m i ⊆ modal-logic-S5-axioms
  modal-logic-S5-axioms-contains-ax-m =
    transitive-leq-subtype
      ( ax-m i)
      ( ax-m i ∪ (ax-b i ∪ ax-4 i))
      ( modal-logic-K-axioms i ∪ (ax-m i ∪ (ax-b i ∪ ax-4 i)))
      ( subtype-union-right
        ( modal-logic-K-axioms i)
        ( ax-m i ∪ (ax-b i ∪ ax-4 i)))
      ( subtype-union-left
        ( ax-m i)
        ( ax-b i ∪ ax-4 i))

  modal-logic-S5-axioms-contains-ax-b : ax-b i ⊆ modal-logic-S5-axioms
  modal-logic-S5-axioms-contains-ax-b =
    transitive-leq-subtype
      ( ax-b i)
      ( ax-m i ∪ (ax-b i ∪ ax-4 i))
      ( modal-logic-K-axioms i ∪ (ax-m i ∪ (ax-b i ∪ ax-4 i)))
      ( subtype-union-right
        ( modal-logic-K-axioms i)
        ( ax-m i ∪ (ax-b i ∪ ax-4 i)))
      ( transitive-leq-subtype
        ( ax-b i)
        ( ax-b i ∪ ax-4 i)
        ( ax-m i ∪ (ax-b i ∪ ax-4 i))
        ( subtype-union-right (ax-m i) (ax-b i ∪ ax-4 i))
        ( subtype-union-left (ax-b i) (ax-4 i)))

  modal-logic-S5-axioms-contains-ax-4 : ax-4 i ⊆ modal-logic-S5-axioms
  modal-logic-S5-axioms-contains-ax-4 =
    transitive-leq-subtype
      ( ax-4 i)
      ( ax-m i ∪ (ax-b i ∪ ax-4 i))
      ( modal-logic-K-axioms i ∪ (ax-m i ∪ (ax-b i ∪ ax-4 i)))
      ( subtype-union-right
        ( modal-logic-K-axioms i)
        ( ax-m i ∪ (ax-b i ∪ ax-4 i)))
      ( transitive-leq-subtype
        ( ax-4 i)
        ( ax-b i ∪ ax-4 i)
        ( ax-m i ∪ (ax-b i ∪ ax-4 i))
        ( subtype-union-right (ax-m i) (ax-b i ∪ ax-4 i))
        ( subtype-union-right (ax-b i) (ax-4 i)))

  modal-logic-S5-contains-ax-m : ax-m i ⊆ modal-logic-S5
  modal-logic-S5-contains-ax-m =
    transitive-leq-subtype
      ( ax-m i)
      ( modal-logic-S5-axioms)
      ( modal-logic-S5)
      ( axioms-subset-modal-logic modal-logic-S5-axioms)
      ( modal-logic-S5-axioms-contains-ax-m)

  modal-logic-S5-contains-ax-b : ax-b i ⊆ modal-logic-S5
  modal-logic-S5-contains-ax-b =
    transitive-leq-subtype
      ( ax-b i)
      ( modal-logic-S5-axioms)
      ( modal-logic-S5)
      ( axioms-subset-modal-logic modal-logic-S5-axioms)
      ( modal-logic-S5-axioms-contains-ax-b)

  modal-logic-S5-contains-ax-4 : ax-4 i ⊆ modal-logic-S5
  modal-logic-S5-contains-ax-4 =
    transitive-leq-subtype
      ( ax-4 i)
      ( modal-logic-S5-axioms)
      ( modal-logic-S5)
      ( axioms-subset-modal-logic modal-logic-S5-axioms)
      ( modal-logic-S5-axioms-contains-ax-4)

module _
  {l1 l2 l3 l4 : Level} (i : Set l1)
  where

  soundness-S5-additional-axioms :
    soundness (ax-m i ∪ (ax-b i ∪ ax-4 i)) (equivalence-kripke-class l2 l3 i l4)
  soundness-S5-additional-axioms =
    soundness-union
      ( ax-m i)
      ( ax-b i ∪ ax-4 i)
      ( reflexive-kripke-class l2 l3 i l4)
      ( symmetry-kripke-class l2 l3 i l4 ∩ transitivity-kripke-class l2 l3 i l4)
      ( ax-m-soundness i l3 l4)
      ( soundness-union
        ( ax-b i)
        ( ax-4 i)
        ( symmetry-kripke-class l2 l3 i l4)
        ( transitivity-kripke-class l2 l3 i l4)
        ( ax-b-soundness i l3 l4)
        ( ax-4-soundness i l3 l4))

  soundness-S5-axioms :
    soundness
      ( modal-logic-S5-axioms i)
      ( decidable-subclass i (equivalence-kripke-class l2 l3 i l4))
  soundness-S5-axioms =
    soundness-union
      ( modal-logic-K-axioms i)
      ( ax-m i ∪ (ax-b i ∪ ax-4 i))
      ( decidable-models l2 l3 i l4)
      ( equivalence-kripke-class l2 l3 i l4)
      ( soundness-K-axioms i)
      ( soundness-S5-additional-axioms)

  soundness-S5 :
    soundness
      ( modal-logic-S5 i)
      ( decidable-subclass i (equivalence-kripke-class l2 l3 i l4))
  soundness-S5 =
    soundness-modal-logic
      ( decidable-subclass i (equivalence-kripke-class l2 l3 i l4))
      ( soundness-S5-axioms)

  soundness-S5-finite :
    soundness
      ( modal-logic-S5 i)
      ( finite-subclass i (equivalence-kripke-class l2 l3 i l4))
  soundness-S5-finite =
    soundness-subclass
      ( modal-logic-S5 i)
      ( decidable-subclass i (equivalence-kripke-class l2 l3 i l4))
      ( finite-subclass i (equivalence-kripke-class l2 l3 i l4))
      ( subtype-both-intersection
        ( decidable-models l2 l3 i l4)
        ( equivalence-kripke-class l2 l3 i l4)
        ( finite-subclass i (equivalence-kripke-class l2 l3 i l4))
        ( transitive-leq-subtype
          ( finite-subclass i (equivalence-kripke-class l2 l3 i l4))
          ( finite-models l2 l3 i l4)
          ( decidable-models l2 l3 i l4)
          ( finite-models-subclass-decidable-models i)
          ( subtype-intersection-left
            ( finite-models l2 l3 i l4)
            ( equivalence-kripke-class l2 l3 i l4)))
        ( subtype-intersection-right
          ( finite-models l2 l3 i l4)
          ( equivalence-kripke-class l2 l3 i l4)))
      ( soundness-S5)

module _
  {l1 : Level} (i : Set l1)
  where

  is-consistent-S5 : is-consistent-modal-logic (modal-logic-S5 i)
  is-consistent-S5 bot-in-logic =
    map-inv-raise
      ( soundness-S5-finite
        ( i)
        ( ⊥)
        ( bot-in-logic)
        ( pair
          ( pair (unit , unit-trunc-Prop star) (λ _ _ → unit-Prop))
          ( λ _ _ → unit-Prop))
        ( pair
          ( triple
            ( is-finite-unit)
            ( λ _ _ → inl star)
            ( λ _ _ → is-decidable-unit))
          ( triple
            ( λ x → star)
            ( λ x y _ → star)
            ( λ x y z _ _ → star)))
        ( star))
```

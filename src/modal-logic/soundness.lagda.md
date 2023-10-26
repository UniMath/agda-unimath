# Modal logic soundness

```agda
module modal-logic.soundness where
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
  {w : Inhabited-Type l3} (C : model-class w l4 i l5 l6)
  where

  soundness : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ l6)
  soundness = logic ⊆ (class-modal-logic C)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {i : Set l1} {axioms : formulas l2 i}
  {w : Inhabited-Type l3} (C : model-class w l4 i l5 l6)
  where

  soundness-axioms :
    ((a : formula i) → is-in-subtype axioms a → type-Prop (C ⊨C a)) →
    {a : formula i} → axioms ⊢ a → type-Prop (C ⊨C a)
  soundness-axioms H (ax x) = H _ x
  soundness-axioms H (mp dab da) M in-class x =
    soundness-axioms H dab M in-class x (soundness-axioms H da M in-class x)
  soundness-axioms H (nec d) M in-class _ y _ =
    soundness-axioms H d M in-class y

  soundness-deduction :
    ((a : formula i) → is-in-subtype axioms a → type-Prop (C ⊨C a)) →
    soundness (modal-logic axioms) C
  soundness-deduction H a =
    map-universal-property-trunc-Prop (C ⊨C a) (soundness-axioms H)
```

## Properties

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {i : Set l1} (ax₁ : formulas l2 i) (ax₂ : formulas l3 i)
  {w : Inhabited-Type l4}
  (C₁ : model-class w l5 i l6 l7) (C₂ : model-class w l5 i l6 l8)
  (sound₁ : soundness ax₁ C₁) (sound₂ : soundness ax₂ C₂)
  where

  forces-in-intersection :
    (M : kripke-model w l5 i l6) →
    is-in-subtype (intersection-subtype C₁ C₂) M →
    (a : formula i) →
    is-in-subtype ax₁ a + is-in-subtype ax₂ a →
    type-Prop (M ⊨M a)
  forces-in-intersection M in-class a (inl d) =
    sound₁ a d M (subtype-intersection-left C₁ C₂ M in-class)
  forces-in-intersection M in-class a (inr d) =
    sound₂ a d M (subtype-intersection-right C₁ C₂ M in-class)

  soundness-union :
    soundness (union-subtype ax₁ ax₂) (intersection-subtype C₁ C₂)
  soundness-union a is-ax M in-class =
    apply-universal-property-trunc-Prop
      ( is-ax)
      ( M ⊨M a)
      ( forces-in-intersection M in-class a)

  soundness-modal-logic-union :
    soundness (modal-logic (union-subtype ax₁ ax₂)) (intersection-subtype C₁ C₂)
  soundness-modal-logic-union =
    soundness-deduction (intersection-subtype C₁ C₂) soundness-union

module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {i : Set l1} (ax₁ : formulas l2 i) (ax₂ : formulas l3 i)
  {w : Inhabited-Type l4}
  (C₁ : model-class w l5 i l6 l7) (C₂ : model-class w l5 i l6 l7)
  (sound₁ : soundness ax₁ C₁) (sound₂ : soundness ax₂ C₂)
  where

  soundness-modal-logic-union-subclass-left :
    C₁ ⊆ C₂ →
    soundness (modal-logic (union-subtype ax₁ ax₂)) C₁
  soundness-modal-logic-union-subclass-left C₁-sub-C₂ =
    tr
      ( soundness (modal-logic (union-subtype ax₁ ax₂)))
      ( intersection-subtype-left C₁ C₂ C₁-sub-C₂)
      ( soundness-modal-logic-union ax₁ ax₂ C₁ C₂ sound₁ sound₂)

module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {i : Set l1} (ax₁ : formulas l2 i) (ax₂ : formulas l3 i)
  {w : Inhabited-Type l4}
  (C : model-class w l5 i l6 l7)
  (sound₁ : soundness ax₁ C) (sound₂ : soundness ax₂ C)
  where

  soundness-union-same-class : soundness (union-subtype ax₁ ax₂) C
  soundness-union-same-class =
    tr
      ( soundness (union-subtype ax₁ ax₂))
      ( is-reflexivity-intersection C)
      ( soundness-union ax₁ ax₂ C C sound₁ sound₂)

  soundness-modal-logic-union-same-class :
    soundness (modal-logic (union-subtype ax₁ ax₂)) C
  soundness-modal-logic-union-same-class =
    soundness-deduction C soundness-union-same-class
```

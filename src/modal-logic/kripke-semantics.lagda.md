# Krikpe semantics

```agda
module modal-logic.kripke-semantics where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.universe-levels

open import modal-logic.formulas

open import univalent-combinatorics.finite-types
```

</details>

## Idea

TODO

## Definition

### Semantics

```agda
module _
  {l1 : Level} (w : Inhabited-Type l1) (l2 : Level)
  where

  record kripke-frame : UU (l1 ⊔ lsuc l2) where
    constructor frame
    field
      frame-relation : Relation-Prop l2 (type-Inhabited-Type w)
  open kripke-frame public

module _
  {l1 : Level} (w : Inhabited-Type l1)
  (l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  where

  record kripke-model : UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4) where
    constructor model
    field
      model-frame : kripke-frame w l2
      model-valuate : type-Set i → type-Inhabited-Type w → Prop l4
  open kripke-model public

  finite-model : UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4)
  finite-model = kripke-model × is-finite (type-Inhabited-Type w)

module _
  {l1 l2 l3 l4 : Level} {w : Inhabited-Type l1} {i : Set l3}
  where

  model-relation : kripke-model w l2 i l4 → Relation l2 (type-Inhabited-Type w)
  model-relation = type-Relation-Prop ∘ frame-relation ∘ model-frame

  private
    l = l1 ⊔ l2 ⊔ l4

  infix 5 _⊨_
  infix 5 _⊭_
  infix 5 _⊨M_
  infix 5 _⊭M_

  _⊨_ : kripke-model w l2 i l4 × (type-Inhabited-Type w) → formula i → Prop l
  (M , x) ⊨ var n = raise-Prop l (model-valuate M n x)
  (M , x) ⊨ ⊥ = raise-empty-Prop l
  (M , x) ⊨ a ⇒ b = implication-Prop ((M , x) ⊨ a) ((M , x) ⊨ b)
  (M , x) ⊨ □ a =
    Π-Prop
      ( type-Inhabited-Type w)
      ( λ y -> function-Prop (model-relation M x y) ((M , y) ⊨ a))

  _⊭_ : kripke-model w l2 i l4 × (type-Inhabited-Type w) → formula i → Prop l
  (M , x) ⊭ a = neg-Prop ((M , x) ⊨ a)

  _⊨M_ : kripke-model w l2 i l4 → formula i → Prop l
  M ⊨M a = Π-Prop (type-Inhabited-Type w) (λ x → (M , x) ⊨ a)

  _⊭M_ : kripke-model w l2 i l4 → formula i → Prop l
  M ⊭M a = neg-Prop (M ⊨M a)

module _
  {l1 l2 l3 l4 : Level} {w : Inhabited-Type l1} {i : Set l3}
  where

  private
    l = l1 ⊔ l2 ⊔ l3 ⊔ l4

  is-decidable-model-Prop : kripke-model w l2 i l4 → Prop l
  is-decidable-model-Prop M =
    Π-Prop
      ( formula i)
      ( λ a →
        Π-Prop (type-Inhabited-Type w) (λ x → is-decidable-Prop ((M , x) ⊨ a)))

  is-decidable-model : kripke-model w l2 i l4 → UU l
  is-decidable-model = type-Prop ∘ is-decidable-model-Prop

decidable-model :
  {l1 : Level} (w : Inhabited-Type l1)
  (l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level) →
  UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4)
decidable-model w l2 i l4 = Σ (kripke-model w l2 i l4) is-decidable-model
```

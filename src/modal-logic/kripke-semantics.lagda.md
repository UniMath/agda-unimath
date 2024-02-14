# Krikpe semantics

```agda
module modal-logic.kripke-semantics where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import modal-logic.formulas
open import modal-logic.logic-syntax

open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

TODO

## Definition

### Semantics

```agda
module _
  {l1 : Level} (w : UU l1) (l2 : Level)
  where

  kripke-frame : UU (l1 ⊔ lsuc l2)
  kripke-frame = is-inhabited w × Relation-Prop l2 w

module _
  {l1 l2 : Level} {w : UU l1}
  where

  frame-inhabited : kripke-frame w l2 → is-inhabited w
  frame-inhabited = pr1

  frame-relation-Prop : kripke-frame w l2 → Relation-Prop l2 w
  frame-relation-Prop = pr2

  frame-relation : kripke-frame w l2 → Relation l2 w
  frame-relation = type-Relation-Prop ∘ frame-relation-Prop

module _
  {l1 : Level} (w : UU l1)
  (l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  where

  kripke-model : UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4)
  kripke-model = kripke-frame w l2 × (type-Set i → w → Prop l4)

  model-class : (l5 : Level) → UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5)
  model-class l5 = subtype l5 kripke-model

  all-models : model-class lzero
  all-models _ = unit-Prop

  all-models-is-largest-class :
    {l : Level} (C : model-class l) → C ⊆ all-models
  all-models-is-largest-class _ _ _ = star

module _
  {l1 l2 l3 l4 : Level} {w : UU l1} (i : Set l3)
  where

  model-frame : kripke-model w l2 i l4 → kripke-frame w l2
  model-frame = pr1

  model-valuate :
    kripke-model w l2 i l4 → type-Set i → w → Prop l4
  model-valuate = pr2

  model-relation-Prop : kripke-model w l2 i l4 → Relation-Prop l2 w
  model-relation-Prop = frame-relation-Prop ∘ model-frame

  model-relation : kripke-model w l2 i l4 → Relation l2 w
  model-relation = frame-relation ∘ model-frame

module _
  {l1 l2 l3 l4 : Level} {w : UU l1} {i : Set l3}
  where

  private
    l = l1 ⊔ l2 ⊔ l4

  infix 5 _⊨_
  infix 5 _⊭_
  infix 5 _⊨M_
  infix 5 _⊭M_

  _⊨_ : kripke-model w l2 i l4 × w → formula i → Prop l
  (M , x) ⊨ var n = raise-Prop l (model-valuate i M n x)
  (M , x) ⊨ ⊥ = raise-empty-Prop l
  (M , x) ⊨ a →ₘ b = implication-Prop ((M , x) ⊨ a) ((M , x) ⊨ b)
  (M , x) ⊨ □ a =
    Π-Prop
      ( w)
      ( λ y → function-Prop (model-relation i M x y) ((M , y) ⊨ a))

  _⊭_ : kripke-model w l2 i l4 × w → formula i → Prop l
  (M , x) ⊭ a = neg-Prop ((M , x) ⊨ a)

  _⊨M_ : kripke-model w l2 i l4 → formula i → Prop l
  M ⊨M a = Π-Prop w (λ x → (M , x) ⊨ a)

  _⊭M_ : kripke-model w l2 i l4 → formula i → Prop l
  M ⊭M a = neg-Prop (M ⊨M a)

  decidable-class : model-class w l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  decidable-class M = Π-Prop (formula i) (λ a → M ⊨M a)

module _
  {l1 l2 l3 l4 : Level} {w : UU l1} {i : Set l3}
  where

  _⊨C_ :
    {l5 : Level} →
    model-class w l2 i l4 l5 →
    formula i →
    Prop (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5)
  C ⊨C a =
    Π-Prop
      ( kripke-model w l2 i l4)
      ( λ M → function-Prop (is-in-subtype C M) (M ⊨M a))

  class-modal-logic :
    {l5 : Level} →
    model-class w l2 i l4 l5 →
    formulas (l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5) i
  class-modal-logic C a = C ⊨C a

  -- TODO: rename
  class-modal-logic-monotic :
    {l5 l6 : Level}
    (C₁ : model-class w l2 i l4 l5)
    (C₂ : model-class w l2 i l4 l6) →
    C₁ ⊆ C₂ →
    class-modal-logic C₂ ⊆ class-modal-logic C₁
  class-modal-logic-monotic C₁ C₂ sub _ in-modal-logic-C₂ M in-C₁ =
    in-modal-logic-C₂ M (sub M in-C₁)

module _
  {l1 : Level} (w : UU l1)
  (l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  where

  decidable-models : model-class w l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  decidable-models M =
    Π-Prop
      ( formula i)
      ( λ a → (Π-Prop w (λ x → is-decidable-Prop ((M , x) ⊨ a))))

  finite-models : model-class w l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  finite-models M =
    product-Prop
      ( is-finite-Prop w)
      ( product-Prop
        ( Π-Prop
          ( w)
          ( λ x →
            ( Π-Prop ( w)
            ( λ y → is-decidable-Prop (model-relation-Prop i M x y)))))
        ( Π-Prop
          ( w)
          ( λ x →
            ( Π-Prop
              ( type-Set i)
              ( λ n → is-decidable-Prop (model-valuate i M n x))))))

  finite-models-subclass-decidable-models : finite-models ⊆ decidable-models
  finite-models-subclass-decidable-models M (_ , _ , dec-v) (var n) x =
    is-decidable-raise (l1 ⊔ l2 ⊔ l4) _ (dec-v x n)
  finite-models-subclass-decidable-models M _ ⊥ x =
    inr map-inv-raise
  finite-models-subclass-decidable-models M is-fin (a →ₘ b) x =
    is-decidable-function-type
      ( finite-models-subclass-decidable-models M is-fin a x)
      ( finite-models-subclass-decidable-models M is-fin b x)
  finite-models-subclass-decidable-models
    M is-fin@(w-is-fin , dec-r , dec-v) (□ a) x =
      is-decidable-Π-is-finite
        ( w-is-fin)
        ( λ y →
          ( is-decidable-function-type
            ( dec-r x y)
            ( finite-models-subclass-decidable-models M is-fin a y)))
```

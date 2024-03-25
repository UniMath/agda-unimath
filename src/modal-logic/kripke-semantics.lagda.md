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

module _
  (l1 l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  where

  model-with-world : UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4)
  model-with-world = Σ (UU l1) (λ w → kripke-model w l2 i l4)

  world-model-with-world : model-with-world → UU l1
  world-model-with-world = pr1

  model-with-world-model :
    (M : model-with-world) → kripke-model (world-model-with-world M) l2 i l4
  model-with-world-model = pr2

  model-class : (l5 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5)
  model-class l5 = subtype l5 model-with-world

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

  model-valuate : kripke-model w l2 i l4 → type-Set i → w → Prop l4
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

module _
  {l1 l2 l3 l4 : Level} {i : Set l3}
  where

  _⊨C_ :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    formula i →
    Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5)
  C ⊨C a =
    Π-Prop
      ( UU l1)
      ( λ w →
        ( Π-Prop
          ( kripke-model w l2 i l4))
          ( λ M → function-Prop (is-in-subtype C (w , M)) (M ⊨M a)))

  class-modal-logic :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    formulas (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5) i
  class-modal-logic C a = C ⊨C a

  -- TODO: rename
  class-modal-logic-monotic :
    {l5 l6 : Level}
    (C₁ : model-class l1 l2 i l4 l5)
    (C₂ : model-class l1 l2 i l4 l6) →
    C₁ ⊆ C₂ →
    class-modal-logic C₂ ⊆ class-modal-logic C₁
  class-modal-logic-monotic C₁ C₂ sub _ in-modal-logic-C₂ w M in-C₁ =
    in-modal-logic-C₂ w M (sub (w , M) in-C₁)

module _
  (l1 l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  where

  decidable-models : model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  decidable-models (w , M) =
    Π-Prop
      ( formula i)
      (λ a → Π-Prop w (λ x → is-decidable-Prop ((M , x) ⊨ a)))
      -- (λ a → is-decidable-Prop (M ⊨M a))

  finite-models : model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  finite-models (w , M) =
    product-Prop
      ( is-finite-Prop w)
      ( product-Prop
        ( Π-Prop
          ( w)
          ( λ x →
            ( Π-Prop
              ( w)
              ( λ y → is-decidable-Prop (model-relation-Prop i M x y)))))
        ( Π-Prop
          ( w)
          ( λ x →
            ( Π-Prop
              ( type-Set i)
              ( λ n → is-decidable-Prop (model-valuate i M n x))))))

  finite-models-subclass-decidable-models :
    finite-models ⊆ decidable-models
  finite-models-subclass-decidable-models (w , M) (w-is-fin , dec-r , dec-v) =
    lemma
    where
    lemma :
      (a : formula i) (x : w) → is-decidable (type-Prop ((M , x) ⊨ a))
    lemma (var n) x =
      is-decidable-raise (l1 ⊔ l2 ⊔ l4) _ (dec-v x n)
    lemma ⊥ x =
      inr map-inv-raise
    lemma (a →ₘ b) x =
      is-decidable-function-type (lemma a x) (lemma b x)
    lemma (□ a) x =
      is-decidable-Π-is-finite
        ( w-is-fin)
        ( λ y → is-decidable-function-type (dec-r x y) (lemma a y))
```

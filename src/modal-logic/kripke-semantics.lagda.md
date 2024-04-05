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
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.iterated-dependent-product-types
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.identity-types

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
  (l1 l2 : Level)
  where

  kripke-frame : UU (lsuc l1 ⊔ lsuc l2)
  kripke-frame = Σ (Inhabited-Type l1) (Relation-Prop l2 ∘ type-Inhabited-Type)

module _
  {l1 l2 : Level}
  where

  -- TODO: replace with theorem
  postulate
    is-set-kripke-frame : is-set (kripke-frame l1 l2)

  Inhabited-Type-kripke-frame : kripke-frame l1 l2 → Inhabited-Type l1
  Inhabited-Type-kripke-frame = pr1

  type-kripke-frame : kripke-frame l1 l2 → UU l1
  type-kripke-frame = type-Inhabited-Type ∘ Inhabited-Type-kripke-frame

  is-inhabited-type-kripke-frame :
    (F : kripke-frame l1 l2) → is-inhabited (type-kripke-frame F)
  is-inhabited-type-kripke-frame =
    is-inhabited-type-Inhabited-Type ∘ Inhabited-Type-kripke-frame

  relation-Prop-kripke-frame :
    (F : kripke-frame l1 l2) → Relation-Prop l2 (type-kripke-frame F)
  relation-Prop-kripke-frame = pr2

  relation-kripke-frame :
    (F : kripke-frame l1 l2) → Relation l2 (type-kripke-frame F)
  relation-kripke-frame = type-Relation-Prop ∘ relation-Prop-kripke-frame

module _
  (l1 l2 : Level) {l3 : Level} (i : Set l3) (l4 : Level)
  where

  kripke-model : UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4)
  kripke-model =
    Σ (kripke-frame l1 l2) (λ F → type-Set i → type-kripke-frame F → Prop l4)

module _
  {l1 l2 l3 l4 : Level} (i : Set l3)
  where

  kripke-frame-kripke-model : kripke-model l1 l2 i l4 → kripke-frame l1 l2
  kripke-frame-kripke-model = pr1

  Inhabited-Type-kripke-model : kripke-model l1 l2 i l4 → Inhabited-Type l1
  Inhabited-Type-kripke-model =
    Inhabited-Type-kripke-frame ∘ kripke-frame-kripke-model

  type-kripke-model : kripke-model l1 l2 i l4 → UU l1
  type-kripke-model = type-kripke-frame ∘ kripke-frame-kripke-model

  is-inhabited-type-kripke-model :
    (M : kripke-model l1 l2 i l4) → is-inhabited (type-kripke-model M)
  is-inhabited-type-kripke-model =
    is-inhabited-type-kripke-frame ∘ kripke-frame-kripke-model

  relation-Prop-kripke-model :
    (M : kripke-model l1 l2 i l4) → Relation-Prop l2 (type-kripke-model M)
  relation-Prop-kripke-model =
    relation-Prop-kripke-frame ∘ kripke-frame-kripke-model

  relation-kripke-model :
    (M : kripke-model l1 l2 i l4) → Relation l2 (type-kripke-model M)
  relation-kripke-model =
    relation-kripke-frame ∘ kripke-frame-kripke-model

  valuate-kripke-model :
    (M : kripke-model l1 l2 i l4) → type-Set i → type-kripke-model M → Prop l4
  valuate-kripke-model = pr2

module _
  (l1 l2 : Level) {l3 : Level} (i : Set l3) (l4 : Level)
  where

  model-class : (l5 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5)
  model-class l5 = subtype l5 (kripke-model l1 l2 i l4)

  all-models : model-class lzero
  all-models _ = unit-Prop

module _
  {l1 l2 l3 l4 : Level} (i : Set l3)
  where

  all-models-is-largest-class :
    {l5 : Level} (C : model-class l1 l2 i l4 l5) → C ⊆ all-models l1 l2 i l4
  all-models-is-largest-class _ _ _ = star

-- TODO: move to binary relations
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-serial : UU (l1 ⊔ l2)
  is-serial = (x : A) → ∃ A (λ y → R x y)

  is-euclidean : UU (l1 ⊔ l2)
  is-euclidean = (x y z : A) → R x y → R x z → R y z

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-serial-Relation-Prop : UU (l1 ⊔ l2)
  is-serial-Relation-Prop = is-serial (type-Relation-Prop R)

  is-prop-is-serial-Relation-Prop : is-prop is-serial-Relation-Prop
  is-prop-is-serial-Relation-Prop =
    is-prop-Π (λ x → is-prop-∃ A _)

  is-euclidean-Relation-Prop : UU (l1 ⊔ l2)
  is-euclidean-Relation-Prop = is-euclidean (type-Relation-Prop R)

  is-prop-is-euclidean-Relation-Prop : is-prop is-euclidean-Relation-Prop
  is-prop-is-euclidean-Relation-Prop =
    is-prop-iterated-Π 3
      ( λ x y z →
        ( is-prop-function-type
          ( is-prop-function-type (is-prop-type-Relation-Prop R y z))))

module _
  (l1 l2 : Level) {l3 : Level} (i : Set l3) (l4 : Level)
  where

  relation-property-class :
    {l5 : Level} →
    ({A : UU l1} → subtype l5 (Relation-Prop l2 A)) →
    model-class l1 l2 i l4 l5
  relation-property-class property M =
    property (relation-Prop-kripke-model i M)

  -- intersection-relation-property-class :
  --   {l5 l6 : Level} →
  --   (R₁ : {A : UU l1} → subtype l5 (Relation-Prop l2 A)) →
  --   (R₂ : {A : UU l1} → subtype l5 (Relation-Prop l2 A)) →
  --   Id
  --     ( intersection-subtype
  --       ( relation-property-class R₁)
  --       ( relation-property-class R₂))
  --     ( relation-property-class (intersection-subtype R₁ R₂))
  -- intersection-relation-property-class R₁ R₂ = refl

  reflexive-kripke-class : model-class l1 l2 i l4 (l1 ⊔ l2)
  reflexive-kripke-class =
    relation-property-class
      ( λ x →
        ( is-reflexive-Relation-Prop x , is-prop-is-reflexive-Relation-Prop x))

  symmetry-kripke-class : model-class l1 l2 i l4 (l1 ⊔ l2)
  symmetry-kripke-class =
    relation-property-class
      ( λ x →
        ( is-symmetric-Relation-Prop x , is-prop-is-symmetric-Relation-Prop x))

  transitivity-kripke-class : model-class l1 l2 i l4 (l1 ⊔ l2)
  transitivity-kripke-class =
    relation-property-class
      ( λ x →
        ( pair
          ( is-transitive-Relation-Prop x)
          ( is-prop-is-transitive-Relation-Prop x)))

  serial-kripke-class : model-class l1 l2 i l4 (l1 ⊔ l2)
  serial-kripke-class =
    relation-property-class
      ( λ x →
        ( is-serial-Relation-Prop x , is-prop-is-serial-Relation-Prop x))

  euclidean-kripke-class : model-class l1 l2 i l4 (l1 ⊔ l2)
  euclidean-kripke-class =
    relation-property-class
      ( λ x →
        ( is-euclidean-Relation-Prop x , is-prop-is-euclidean-Relation-Prop x))

  equivalence-kripke-class : model-class l1 l2 i l4 (l1 ⊔ l2)
  equivalence-kripke-class =
    relation-property-class is-equivalence-relation-Prop

module _
  {l1 l2 l3 l4 : Level} {i : Set l3}
  where

  infix 5 _⊨_
  infix 5 _⊭_
  infix 5 _⊨M_
  infix 5 _⊭M_

  _⊨_ :
    Σ (kripke-model l1 l2 i l4) (type-kripke-model i) →
    formula i →
    Prop (l1 ⊔ l2 ⊔ l4)
  (M , x) ⊨ var n = raise-Prop (l1 ⊔ l2) (valuate-kripke-model i M n x)
  (M , x) ⊨ ⊥ = raise-empty-Prop (l1 ⊔ l2 ⊔ l4)
  (M , x) ⊨ a →ₘ b = implication-Prop ((M , x) ⊨ a) ((M , x) ⊨ b)
  (M , x) ⊨ □ a =
    Π-Prop
      ( type-kripke-model i M)
      ( λ y → function-Prop (relation-kripke-model i M x y) ((M , y) ⊨ a))

  _⊭_ :
    Σ (kripke-model l1 l2 i l4) (type-kripke-model i) →
    formula i →
    Prop (l1 ⊔ l2 ⊔ l4)
  (M , x) ⊭ a = neg-Prop ((M , x) ⊨ a)

  _⊨M_ : kripke-model l1 l2 i l4 → formula i → Prop (l1 ⊔ l2 ⊔ l4)
  M ⊨M a = Π-Prop (type-kripke-model i M) (λ x → (M , x) ⊨ a)

  _⊭M_ : kripke-model l1 l2 i l4 → formula i → Prop (l1 ⊔ l2 ⊔ l4)
  M ⊭M a = neg-Prop (M ⊨M a)

  _⊨C_ :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    formula i →
    Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5)
  C ⊨C a =
    Π-Prop
      ( kripke-model l1 l2 i l4)
      ( λ M → function-Prop (is-in-subtype C M) (M ⊨M a))

  class-modal-logic :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    formulas (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5) i
  class-modal-logic = _⊨C_

  -- TODO: rename
  class-modal-logic-monotic :
    {l5 l6 : Level}
    (C₁ : model-class l1 l2 i l4 l5)
    (C₂ : model-class l1 l2 i l4 l6) →
    C₁ ⊆ C₂ →
    class-modal-logic C₂ ⊆ class-modal-logic C₁
  class-modal-logic-monotic C₁ C₂ sub _ in-modal-logic-C₂ M in-C₁ =
    in-modal-logic-C₂ M (sub M in-C₁)

module _
  {l1 l2 : Level}
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  where

  kripke-frame-model-class :
    kripke-frame l1 l2 →
    model-class l1 l2 i l4 (lsuc l1 ⊔ lsuc l2)
  pr1 (kripke-frame-model-class F M) =
    kripke-frame-kripke-model i M ＝ F
  pr2 (kripke-frame-model-class F M) =
    is-set-kripke-frame (kripke-frame-kripke-model i M) F

  -- frame-modal-logic :
  --   kripke-frame l1 l2 →
  --   formulas (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4) i
  -- frame-modal-logic F a =
  --   Π-Prop
  --     ( type-Set i → type-kripke-frame F → Prop l4)
  --     ( λ v → (F , v) ⊨M a)

module _
  (l1 l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  where

  decidable-models : model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  decidable-models M =
    Π-Prop
      ( formula i)
      ( λ a →
        ( Π-Prop
          ( type-kripke-model i M)
          ( λ x → is-decidable-Prop ((M , x) ⊨ a))))

  -- TODO: maybe dicidable-finite?
  finite-models : model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  finite-models M =
    product-Prop
      ( is-finite-Prop (type-kripke-model i M))
      ( product-Prop
        ( Π-Prop
          ( type-kripke-model i M)
          ( λ x →
            ( Π-Prop
              ( type-kripke-model i M)
              ( λ y → is-decidable-Prop (relation-Prop-kripke-model i M x y)))))
        ( Π-Prop
          ( type-kripke-model i M)
          ( λ x →
            ( Π-Prop
              ( type-Set i)
              ( λ n → is-decidable-Prop (valuate-kripke-model i M n x))))))

module _
  {l1 l2 l3 l4 : Level} (i : Set l3)
  where

  finite-models-subclass-decidable-models :
    finite-models l1 l2 i l4 ⊆ decidable-models l1 l2 i l4
  finite-models-subclass-decidable-models M (w-is-fin , dec-r , dec-v) = lemma
    where
    lemma :
      (a : formula i) (x : type-kripke-model i M) →
      is-decidable (type-Prop ((M , x) ⊨ a))
    lemma (var n) x =
      is-decidable-raise (l1 ⊔ l2) _ (dec-v x n)
    lemma ⊥ x =
      inr map-inv-raise
    lemma (a →ₘ b) x =
      is-decidable-function-type (lemma a x) (lemma b x)
    lemma (□ a) x =
      is-decidable-Π-is-finite
        ( w-is-fin)
        ( λ y → is-decidable-function-type (dec-r x y) (lemma a y))

  is-finite-model-valuate-decidable-models :
    (M : kripke-model l1 l2 i l4) →
    is-in-subtype (finite-models l1 l2 i l4) M →
    (a : formula i) →
    is-decidable (type-Prop (M ⊨M a))
  is-finite-model-valuate-decidable-models M sub-fin a =
    is-decidable-Π-is-finite
      ( pr1 (sub-fin))
      ( finite-models-subclass-decidable-models M sub-fin a)

  decidable-subclass :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  decidable-subclass C = intersection-subtype (decidable-models l1 l2 i l4) C

  finite-subclass :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  finite-subclass C = intersection-subtype (finite-models l1 l2 i l4) C
```

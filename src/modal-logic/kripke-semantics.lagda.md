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
open import foundation.law-of-excluded-middle
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

open import modal-logic.deduction
open import modal-logic.formulas

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
  (l1 l2 : Level) {l3 : Level} (i : Set l3) (l4 : Level)
  where

  kripke-model : UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4)
  kripke-model =
    Σ ( Inhabited-Type l1)
      ( λ w →
        ( product
          ( Relation-Prop l2 (type-Inhabited-Type w))
          ( type-Set i → type-Inhabited-Type w → Prop l4)))

module _
  {l1 l2 l3 l4 : Level} (i : Set l3)
  where

  Inhabited-Type-kripke-model : kripke-model l1 l2 i l4 → Inhabited-Type l1
  Inhabited-Type-kripke-model = pr1

  type-kripke-model : kripke-model l1 l2 i l4 → UU l1
  type-kripke-model = type-Inhabited-Type ∘ Inhabited-Type-kripke-model

  is-inhabited-type-kripke-model :
    (M : kripke-model l1 l2 i l4) → is-inhabited (type-kripke-model M)
  is-inhabited-type-kripke-model =
    is-inhabited-type-Inhabited-Type ∘ Inhabited-Type-kripke-model

  relation-Prop-kripke-model :
    (M : kripke-model l1 l2 i l4) → Relation-Prop l2 (type-kripke-model M)
  relation-Prop-kripke-model = pr1 ∘ pr2

  relation-kripke-model :
    (M : kripke-model l1 l2 i l4) → Relation l2 (type-kripke-model M)
  relation-kripke-model = type-Relation-Prop ∘ relation-Prop-kripke-model

  valuate-kripke-model :
    (M : kripke-model l1 l2 i l4) → type-Set i → type-kripke-model M → Prop l4
  valuate-kripke-model = pr2 ∘ pr2

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
  -- is-serial = (x : A) → ∃ A (λ y → R x y)
  is-serial = (x : A) → exists-structure A (λ y → R x y)

  is-euclidean : UU (l1 ⊔ l2)
  is-euclidean = (x y z : A) → R x y → R x z → R y z

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-serial-Relation-Prop : UU (l1 ⊔ l2)
  is-serial-Relation-Prop = is-serial (type-Relation-Prop R)

  is-prop-is-serial-Relation-Prop : is-prop is-serial-Relation-Prop
  is-prop-is-serial-Relation-Prop =
    is-prop-Π (λ x → is-prop-exists-structure A _)

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

  reflexive-kripke-models : model-class l1 l2 i l4 (l1 ⊔ l2)
  reflexive-kripke-models =
    relation-property-class
      ( λ x →
        ( is-reflexive-Relation-Prop x , is-prop-is-reflexive-Relation-Prop x))

  symmetry-kripke-models : model-class l1 l2 i l4 (l1 ⊔ l2)
  symmetry-kripke-models =
    relation-property-class
      ( λ x →
        ( is-symmetric-Relation-Prop x , is-prop-is-symmetric-Relation-Prop x))

  transitive-kripke-models : model-class l1 l2 i l4 (l1 ⊔ l2)
  transitive-kripke-models =
    relation-property-class
      ( λ x →
        ( pair
          ( is-transitive-Relation-Prop x)
          ( is-prop-is-transitive-Relation-Prop x)))

  serial-kripke-models : model-class l1 l2 i l4 (l1 ⊔ l2)
  serial-kripke-models =
    relation-property-class
      ( λ x →
        ( is-serial-Relation-Prop x , is-prop-is-serial-Relation-Prop x))

  euclidean-kripke-models : model-class l1 l2 i l4 (l1 ⊔ l2)
  euclidean-kripke-models =
    relation-property-class
      ( λ x →
        ( is-euclidean-Relation-Prop x , is-prop-is-euclidean-Relation-Prop x))

  equivalence-kripke-models : model-class l1 l2 i l4 (l1 ⊔ l2)
  equivalence-kripke-models =
    relation-property-class is-equivalence-relation-Prop

module _
  {l1 l2 l3 l4 : Level} {i : Set l3}
  where

  infix 7 _⊨ₘ_
  infix 7 _⊨Mₘ_
  infix 7 _⊨Cₘ_

  _⊨ₘ_ :
    Σ (kripke-model l1 l2 i l4) (type-kripke-model i) →
    modal-formula i →
    Prop (l1 ⊔ l2 ⊔ l4)
  (M , x) ⊨ₘ varₘ n = raise-Prop (l1 ⊔ l2) (valuate-kripke-model i M n x)
  (M , x) ⊨ₘ ⊥ₘ = raise-empty-Prop (l1 ⊔ l2 ⊔ l4)
  (M , x) ⊨ₘ a →ₘ b = (M , x) ⊨ₘ a ⇒ (M , x) ⊨ₘ b
  (M , x) ⊨ₘ □ₘ a =
    Π-Prop
      ( type-kripke-model i M)
      ( λ y → function-Prop (relation-kripke-model i M x y) ((M , y) ⊨ₘ a))

  _⊨Mₘ_ : kripke-model l1 l2 i l4 → modal-formula i → Prop (l1 ⊔ l2 ⊔ l4)
  M ⊨Mₘ a = Π-Prop (type-kripke-model i M) (λ x → (M , x) ⊨ₘ a)

  _⊨Cₘ_ :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    modal-formula i →
    Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5)
  C ⊨Cₘ a =
    Π-Prop
      ( kripke-model l1 l2 i l4)
      ( λ M → function-Prop (is-in-subtype C M) (M ⊨Mₘ a))

  class-modal-logic :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    modal-theory (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5) i
  class-modal-logic = _⊨Cₘ_

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
  (l1 l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  where

  decidable-kripke-models : model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  decidable-kripke-models M =
    Π-Prop
      ( modal-formula i)
      ( λ a →
        ( Π-Prop
          ( type-kripke-model i M)
          ( λ x → is-decidable-Prop ((M , x) ⊨ₘ a))))

  finite-kripke-models : model-class l1 l2 i l4 l1
  finite-kripke-models = is-finite-Prop ∘ type-kripke-model i

  finite-decidable-kripke-models : model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  finite-decidable-kripke-models M =
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

  finite-decidable-subclass-decidable-models :
    finite-decidable-kripke-models l1 l2 i l4 ⊆
      decidable-kripke-models l1 l2 i l4
  finite-decidable-subclass-decidable-models M (w-is-fin , dec-r , dec-v) =
    lemma
    where
    lemma :
      (a : modal-formula i) (x : type-kripke-model i M) →
      is-decidable (type-Prop ((M , x) ⊨ₘ a))
    lemma (varₘ n) x =
      is-decidable-raise (l1 ⊔ l2) _ (dec-v x n)
    lemma ⊥ₘ x =
      inr map-inv-raise
    lemma (a →ₘ b) x =
      is-decidable-function-type (lemma a x) (lemma b x)
    lemma (□ₘ a) x =
      is-decidable-Π-is-finite
        ( w-is-fin)
        ( λ y → is-decidable-function-type (dec-r x y) (lemma a y))

  is-finite-model-valuate-decidable-kripke-models :
    (M : kripke-model l1 l2 i l4) →
    is-in-subtype (finite-decidable-kripke-models l1 l2 i l4) M →
    (a : modal-formula i) →
    is-decidable (type-Prop (M ⊨Mₘ a))
  is-finite-model-valuate-decidable-kripke-models M sub-fin a =
    is-decidable-Π-is-finite
      ( pr1 (sub-fin))
      ( finite-decidable-subclass-decidable-models M sub-fin a)

  decidable-subclass :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  decidable-subclass C = (decidable-kripke-models l1 l2 i l4) ∩ C

  finite-subclass :
    {l5 : Level} →
    model-class l1 l2 i l4 l5 →
    model-class l1 l2 i l4 (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  finite-subclass C = (finite-decidable-kripke-models l1 l2 i l4) ∩ C

module _
  {l1 l2 l3 l4 : Level} (i : Set l3)
  (lem : LEM (l1 ⊔ l2 ⊔ l4))
  where

  all-models-is-decidable :
    all-models l1 l2 i l4 ⊆ decidable-kripke-models l1 l2 i l4
  all-models-is-decidable M _ a x = lem ((M , x) ⊨ₘ a)

  subset-decidable-subclass-lem :
    {l5 : Level} (C : model-class l1 l2 i l4 l5) →
    C ⊆ decidable-subclass i C
  subset-decidable-subclass-lem C =
    subtype-both-intersection (decidable-kripke-models l1 l2 i l4) C C
      ( transitive-leq-subtype
        ( C)
        ( all-models l1 l2 i l4)
        ( decidable-kripke-models l1 l2 i l4)
        ( all-models-is-decidable)
        ( all-models-is-largest-class i C))
      ( refl-leq-subtype C)
```

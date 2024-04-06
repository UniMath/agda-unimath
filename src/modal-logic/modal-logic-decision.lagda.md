# Modal logic decision

```agda
module modal-logic.modal-logic-decision where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions

open import lists.arrays
open import lists.concatenation-lists
open import lists.lists
open import lists.reversing-lists

open import modal-logic.completeness
open import modal-logic.formulas
open import modal-logic.kripke-models-filtrations
open import modal-logic.kripke-models-filtrations-theorem
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.soundness
open import modal-logic.weak-deduction

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.kuratowsky-finite-sets
open import univalent-combinatorics.small-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (i : Set l3)
  (theory : modal-theory l2 i)
  (C : model-class l1 l2 i l4 l5)
  (C-sub-fin : C ⊆ finite-models l1 l2 i l4)
  (C-is-fin : is-finite (type-subtype C))
  where

  decision-procedure :
    (a : formula i) →
    is-decidable
      ( (M : type-subtype C) → type-Prop (inclusion-subtype C M ⊨M a))
  decision-procedure a =
    is-decidable-Π-is-finite
      ( C-is-fin)
      ( λ (M , M-in-C) →
        ( is-finite-model-valuate-decidable-models i M (C-sub-fin M M-in-C) a))

  decision-procedure' : (a : formula i) → bool
  decision-procedure' a with decision-procedure a
  ... | inl _ = true
  ... | inr _ = false

  decision-procedure-correctness :
    soundness theory C →
    completeness theory C →
    (a : formula i) →
    theory a ⇔ prop-bool (decision-procedure' a)
  pr1 (decision-procedure-correctness sound complete a) in-theory
    with decision-procedure a
  ... | inl _ = star
  ... | inr not-valid-in-C =
      not-valid-in-C (λ (M , M-in-C) x → sound a in-theory M M-in-C x)
  pr2 (decision-procedure-correctness sound complete a) _
    with decision-procedure a
  ... | inl valid-in-C = complete a (λ M M-in-C → valid-in-C (M , M-in-C))

module _
  {l : Level} {i : Set l}
  where

  collect-vars : formula i → list (type-Set i)
  collect-vars (var x) = cons x nil
  collect-vars ⊥ = nil
  collect-vars (a →ₘ b) = concat-list (collect-vars a) (collect-vars b)
  collect-vars (□ a) = collect-vars a

module _
  {l1 l2 l3 l4 l5 : Level} (i : Set l3)
  (F : kripke-frame l1 l2)
  where

  valuates-equals-on-vars :
    {l6 : Level} →
    subtype l6 (type-Set i) →
    (type-Set i → type-kripke-frame F → Prop l4) →
    (type-Set i → type-kripke-frame F → Prop l5) →
    UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  valuates-equals-on-vars vars V V' =
    ((a , _) : type-subtype vars) → (x : type-kripke-frame F) → V a x ⇔ V' a x

  valuates-equals-on-vars-subtype :
    {l6 l7 : Level}
    (vars₁ : subtype l6 (type-Set i))
    (vars₂ : subtype l7 (type-Set i)) →
    vars₂ ⊆ vars₁ →
    (V : type-Set i → type-kripke-frame F → Prop l4)
    (V' : type-Set i → type-kripke-frame F → Prop l5) →
    valuates-equals-on-vars (vars₁) V V' →
    valuates-equals-on-vars (vars₂) V V'
  valuates-equals-on-vars-subtype vars₁ vars₂ sub V V' eq (a , in-vars) =
    eq (a , sub a in-vars)

  affect-only-occured-vars :
    (a : formula i) →
    (V : type-Set i → type-kripke-frame F → Prop l4) →
    (V' : type-Set i → type-kripke-frame F → Prop l5) →
    valuates-equals-on-vars (in-list (collect-vars a)) V V' →
    (x : type-kripke-frame F) →
    (((F , V) , x) ⊨ a) ⇔ (((F , V') , x) ⊨ a)
  affect-only-occured-vars (var n) V V' eq x =
    pair
      ( λ v →
        ( map-raise
          ( forward-implication
            ( eq (n , unit-trunc-Prop (is-head n nil)) x)
            ( map-inv-raise v))))
      ( λ v →
        ( map-raise
          ( backward-implication
            ( eq (n , unit-trunc-Prop (is-head n nil)) x)
            ( map-inv-raise v))))
  affect-only-occured-vars ⊥ V V' eq x =
    (map-raise ∘ map-inv-raise) , (map-raise ∘ map-inv-raise)
  affect-only-occured-vars (a →ₘ b) V V' eq x =
    pair
      ( λ fab fa →
        ( forward-implication
          ( affect-only-occured-vars b V V'
            ( valuates-equals-on-vars-subtype
              ( in-list (collect-vars (a →ₘ b)))
              ( in-list (collect-vars b))
              ( subset-in-concat-right (collect-vars a) (collect-vars b))
              ( V)
              ( V')
              ( eq))
            ( x))
          ( fab
            ( backward-implication
              ( affect-only-occured-vars a V V'
                ( valuates-equals-on-vars-subtype
                  ( in-list (collect-vars (a →ₘ b)))
                  ( in-list (collect-vars a))
                  ( subset-in-concat-left (collect-vars a) (collect-vars b))
                  ( V)
                  ( V')
                  ( eq))
                ( x))
              ( fa)))))
      ( λ fab fa →
        ( backward-implication
          ( affect-only-occured-vars b V V'
            ( valuates-equals-on-vars-subtype
              ( in-list (collect-vars (a →ₘ b)))
              ( in-list (collect-vars b))
              ( subset-in-concat-right (collect-vars a) (collect-vars b))
              ( V)
              ( V')
              ( eq))
            ( x))
          ( fab
            ( forward-implication
              ( affect-only-occured-vars a V V'
                ( valuates-equals-on-vars-subtype
                  ( in-list (collect-vars (a →ₘ b)))
                  ( in-list (collect-vars a))
                  ( subset-in-concat-left (collect-vars a) (collect-vars b))
                  ( V)
                  ( V')
                  ( eq))
                ( x))
              ( fa)))))
  affect-only-occured-vars (□ a) V V' eq x =
    pair
      ( λ f y r →
        ( forward-implication (affect-only-occured-vars a V V' eq y) (f y r)))
      ( λ f y r →
        ( backward-implication (affect-only-occured-vars a V V' eq y) (f y r)))

is-kuratowsky-finite-set-Prop' : {l : Level} → Set l → Prop l
is-kuratowsky-finite-set-Prop' X =
  ∃-Prop (list (type-Set X)) (λ l → (x : type-Set X) → type-Prop (in-list l x))

is-kuratowsky-finite-set' : {l : Level} → Set l → UU l
is-kuratowsky-finite-set' X = type-Prop (is-kuratowsky-finite-set-Prop' X)

is-kuratowsky-finite-set-is-kuratowsky-finite-set' :
  {l : Level} (X : Set l) →
  is-kuratowsky-finite-set' X → is-kuratowsky-finite-set X
is-kuratowsky-finite-set-is-kuratowsky-finite-set' X =
  map-universal-property-trunc-Prop
    ( is-kuratowsky-finite-set-Prop X)
    ( λ (l , all-in-list) →
      ( intro-∃
        ( length-list l)
        ( pair
          ( component-list l)
          ( λ x →
            ( apply-universal-property-trunc-Prop
              ( all-in-list x)
              ( trunc-Prop (fiber _ x))
              ( λ x-in-list →
                ( unit-trunc-Prop
                  ( pair
                    ( index-in-list x l x-in-list)
                    ( inv
                      ( eq-component-list-index-in-list x l x-in-list))))))))))

dependent-map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (l : list A) (f : Σ A (λ a → a ∈-list l) → B) →
  list B
dependent-map-list nil f = nil
dependent-map-list {A = A} {B} (cons x l) f =
  cons (f (x , is-head x l)) (dependent-map-list l f')
  where
  f' : Σ A (λ a → a ∈-list l) → B
  f' (a , in-list) = f (a , is-in-tail a x l in-list)

in-dependent-map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {l : list A} (f : Σ A (λ a → a ∈-list l) → B)
  {a : A} (a-in-l : a ∈-list l) →
  f (a , a-in-l) ∈-list dependent-map-list l f
in-dependent-map-list f (is-head _ l) = is-head _ _
in-dependent-map-list {A = A} {B} f (is-in-tail _ x l a-in-l) =
  is-in-tail _ _ _ (in-dependent-map-list _ a-in-l)

module _
  {l : Level} (i : Set l)
  where

  subformulas-list : formula i → list (formula i)
  subformulas-list a = cons a (rest a)
    where
    rest : formula i → list (formula i)
    rest (var x) = nil
    rest ⊥ = nil
    rest (a →ₘ b) = concat-list (subformulas-list a) (subformulas-list b)
    rest (□ a) = subformulas-list a

  subformulas-list-has-subimpl :
    (a : formula i) {x y : formula i} →
    (x →ₘ y) ∈-list subformulas-list a →
    (x ∈-list subformulas-list a) × (y ∈-list subformulas-list a)
  subformulas-list-has-subimpl .(x →ₘ y) {x} {y} (is-head .(x →ₘ y) _) =
    pair
      ( is-in-tail x (x →ₘ y) _
        ( in-concat-left
          ( subformulas-list x)
          ( subformulas-list y)
          ( is-head x _)))
      ( is-in-tail y (x →ₘ y) _
        ( in-concat-right
          ( subformulas-list x)
          ( subformulas-list y)
          ( is-head y _)))
  subformulas-list-has-subimpl
    (a →ₘ b) {x} {y} (is-in-tail .(x →ₘ y) .(a →ₘ b) _ xy-in-list)
    with
    in-concat-list
      ( subformulas-list a)
      ( subformulas-list b)
      ( x →ₘ y)
      ( xy-in-list)
  ... | inl xy-in-left =
    let (x-in-tail , y-in-tail) = subformulas-list-has-subimpl a xy-in-left
    in pair
      ( is-in-tail x (a →ₘ b) _
        ( in-concat-left (subformulas-list a) (subformulas-list b) x-in-tail))
      ( is-in-tail y (a →ₘ b) _
        ( in-concat-left (subformulas-list a) (subformulas-list b) y-in-tail))
  ... | inr xy-in-right =
    let (x-in-tail , y-in-tail) = subformulas-list-has-subimpl b xy-in-right
    in pair
      ( is-in-tail x (a →ₘ b) _
        ( in-concat-right (subformulas-list a) (subformulas-list b) x-in-tail))
      ( is-in-tail y (a →ₘ b) _
        ( in-concat-right (subformulas-list a) (subformulas-list b) y-in-tail))
  subformulas-list-has-subimpl
    (□ a) {x} {y} (is-in-tail .(x →ₘ y) .(□ a) _ xy-in-list) =
      let (x-in-tail , y-in-tail) = subformulas-list-has-subimpl a xy-in-list
      in (is-in-tail x (□ a) _ x-in-tail) , (is-in-tail y (□ a) _ y-in-tail)

  subformulas-list-has-subbox :
    (a : formula i) {x : formula i} →
    □ x ∈-list subformulas-list a →
    x ∈-list subformulas-list a
  subformulas-list-has-subbox .(□ x) {x} (is-head .(□ x) _) =
    is-in-tail x (□ x) _ (is-head x _)
  subformulas-list-has-subbox
    (a →ₘ b) {x} (is-in-tail .(□ x) .(a →ₘ b) _ x-in-list)
    with
    in-concat-list (subformulas-list a) (subformulas-list b) (□ x) x-in-list
  ... | inl x-in-left =
    is-in-tail x (a →ₘ b) _
      ( in-concat-left (subformulas-list a) (subformulas-list b)
        ( subformulas-list-has-subbox a x-in-left))
  ... | inr x-in-right =
    is-in-tail x (a →ₘ b) _
      ( in-concat-right (subformulas-list a) (subformulas-list b)
        ( subformulas-list-has-subbox b x-in-right))
  subformulas-list-has-subbox (□ a) {x} (is-in-tail .(□ x) .(□ a) _ x-in-list) =
    is-in-tail x (□ a) _ (subformulas-list-has-subbox a x-in-list)

  is-modal-theory-closed-under-subformulas-subformulas-list :
    (a : formula i) →
    is-modal-theory-closed-under-subformulas i (in-list (subformulas-list a))
  is-modal-theory-closed-under-subformulas-subformulas-list a =
    is-modal-theory-closed-under-subformulas-condition
      ( i)
      ( in-list (subformulas-list a))
      ( map-universal-property-trunc-Prop
        ( product-Prop
          ( in-list (subformulas-list a) _)
          ( in-list (subformulas-list a) _))
        ( λ impl-in-list →
          ( let (a-in-list , b-in-list) =
                  subformulas-list-has-subimpl a impl-in-list
            in (unit-trunc-Prop a-in-list) , (unit-trunc-Prop b-in-list))))
      ( map-universal-property-trunc-Prop
        ( in-list (subformulas-list a) _)
        ( unit-trunc-Prop ∘ subformulas-list-has-subbox a))

  subformulas-Set : formula i → Set l
  subformulas-Set a = set-subset (formula-Set i) (in-list (subformulas-list a))

  subformulas-Set-list : (a : formula i) → list (type-Set (subformulas-Set a))
  subformulas-Set-list a =
    dependent-map-list
      ( subformulas-list a)
      ( λ (x , in-list) → x , unit-trunc-Prop in-list)

  is-kuratowsky-finite'-subformulas-list :
    (a : formula i) → is-kuratowsky-finite-set' (subformulas-Set a)
  is-kuratowsky-finite'-subformulas-list a =
    intro-∃
      ( subformulas-Set-list a)
      ( λ (b , trunc-b-in-list) →
        ( apply-universal-property-trunc-Prop
          ( trunc-b-in-list)
          ( in-list (subformulas-Set-list a) (b , trunc-b-in-list))
          ( λ b-in-list →
            ( unit-trunc-Prop
              ( tr
                ( λ i → (b , i) ∈-list subformulas-Set-list a)
                ( eq-is-prop is-prop-type-trunc-Prop)
                ( in-dependent-map-list
                  (λ (x , in-list) → x , unit-trunc-Prop in-list)
                  ( b-in-list)))))))

  is-kuratowsky-finite-subformulas-list :
    (a : formula i) → is-kuratowsky-finite-set (subformulas-Set a)
  is-kuratowsky-finite-subformulas-list a =
    is-kuratowsky-finite-set-is-kuratowsky-finite-set'
      ( subformulas-Set a)
      ( is-kuratowsky-finite'-subformulas-list a)

  is-finite-subformulas-list :
    LEM l →
    (a : formula i) →
    is-finite (type-subtype (in-list (subformulas-list a)))
  is-finite-subformulas-list lem a =
    is-finite-is-kuratowsky-finite-set
      (subformulas-Set a) lem (is-kuratowsky-finite-subformulas-list a)

  is-finite-subtypes-subformulas-list :
    {l2 : Level} →
    LEM l →
    LEM l2 →
    (a : formula i) →
    is-finite (type-subtype (in-list (subformulas-list a)) → Prop l2)
  is-finite-subtypes-subformulas-list lem lem2 a =
    is-finite-function-type
      ( is-finite-subformulas-list lem a)
      ( is-finite-Prop-LEM lem2)

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  (lem : LEM l1)
  (lem2 : LEM (l1 ⊔ l2))
  where

  surjection-from-injection :
    type-Set A →
    injection (type-Set A) (type-Set B) →
    type-Set B → type-Set A
  surjection-from-injection a (f , is-inj) b
    with
      lem2
        ( pair
          ( Σ (type-Set A) (λ a → f a ＝ b))
          ( is-prop-all-elements-equal
            ( λ x y →
              ( eq-pair-Σ
                ( is-inj (pr2 x ∙ inv (pr2 y)))
                ( eq-is-prop (is-set-type-Set B _ _))))))
  ... | inl x = pr1 x
  ... | inr x = a

  is-invertable-surjection-from-injection :
    (a0 : type-Set A) →
    (inj@(f , _) : injection (type-Set A) (type-Set B)) →
    (a : type-Set A) →
    surjection-from-injection a0 inj (f a) ＝ a
  is-invertable-surjection-from-injection a0 (f , is-inj) a
    with
      lem2
        ( pair
          ( Σ (type-Set A) (λ a' → f a' ＝ f a))
          ( is-prop-all-elements-equal
            ( λ x y →
              ( eq-pair-Σ
                ( is-inj (pr2 x ∙ inv (pr2 y)))
                ( eq-is-prop (is-set-type-Set B _ _))))))
  ... | inl x = is-inj (pr2 x)
  ... | inr x = ex-falso (x (a , refl))

  is-surjective-surjection-from-injection :
    (a : type-Set A) →
    (inj : injection (type-Set A) (type-Set B)) →
    is-surjective (surjection-from-injection a inj)
  is-surjective-surjection-from-injection a0 (f , is-inj) a =
    unit-trunc-Prop
      ( f a , is-invertable-surjection-from-injection a0 (f , is-inj) a)

  kuratowsky-finite-set-injection :
    injection (type-Set A) (type-Set B) →
    is-kuratowsky-finite-set B →
    is-kuratowsky-finite-set A
  kuratowsky-finite-set-injection inj b-is-fin
    with lem (is-inhabited-Prop (type-Set A))
  ... | inl x =
    apply-twice-universal-property-trunc-Prop
      ( x)
      ( b-is-fin)
      ( is-kuratowsky-finite-set-Prop A)
      ( λ a (n , e) →
        ( unit-trunc-Prop
          ( triple
            ( n)
            ( surjection-from-injection a inj ∘ pr1 e)
            ( is-surjective-comp
              ( is-surjective-surjection-from-injection a inj)
              ( pr2 e)))))
  ... | inr x =
    is-kuratowsky-finite-set-is-finite A
      ( is-finite-is-empty (x ∘ unit-trunc-Prop))

  is-finite-injection :
    injection (type-Set A) (type-Set B) →
    is-finite (type-Set B) →
    is-finite (type-Set A)
  is-finite-injection inj b-is-fin =
    is-finite-is-kuratowsky-finite-set A
      lem (kuratowsky-finite-set-injection inj
        ( is-kuratowsky-finite-set-is-finite B b-is-fin))

module _
  {l1 l2 l3 l4 l5 : Level} (i : Set l3)
  (M : kripke-model l1 l2 i l4)
  (lem : LEM (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5))
  (theory : modal-theory l5 i)
  (is-fin : is-finite (type-subtype theory))
  where

  is-finite-equivalence-classes-filtration :
    is-finite (equivalence-class (Φ-equivalence i theory M))
  is-finite-equivalence-classes-filtration =
    is-finite-injection
      ( equivalence-class-Set (Φ-equivalence i theory M))
      ( function-Set (type-subtype theory) (Prop-Set (l1 ⊔ l2 ⊔ l4)))
      ( lem)
      ( lem)
      ( injection-map-function-equivalence-class i theory M)
      ( is-finite-function-type
        ( is-fin)
        ( is-finite-Prop-LEM
          ( lower-LEM (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5) lem)))

  is-small-equivalence-classes-filtration :
    (l : Level) → is-small l (equivalence-class (Φ-equivalence i theory M))
  is-small-equivalence-classes-filtration l =
    is-small-is-finite l
      ( pair
        ( equivalence-class (Φ-equivalence i theory M))
        ( is-finite-equivalence-classes-filtration))

module _
  {l1 l2 l3 l4 : Level} (i : Set l3)
  -- (theory : modal-theory l5 i)
  -- (is-fin : is-finite (type-subtype theory))
  (l5 l6 l7 l8 : Level)
  (lem : LEM (l2 ⊔ lsuc l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6 ⊔ lsuc l7 ⊔ lsuc l8))
  where

  filtration-models-subset-finite-models :
    filtration-models l1 l2 i l4 l5 l6 l7 l8 ⊆ finite-models l1 l2 i l4
  filtration-models-subset-finite-models M* =
    map-universal-property-trunc-Prop
      ( finite-models l1 l2 i l4 M*)
      ( λ ((theory , M) , is-fin , t-is-filt) →
        ( apply-universal-property-trunc-Prop
          ( t-is-filt)
          ( finite-models l1 l2 i l4 M*)
          ( λ is-filt →
            ( triple
              ( is-finite-equiv
                ( equiv-is-kripke-model-filtration i theory M M* is-filt)
                ( is-finite-equivalence-classes-filtration i M
                  ( lower-LEM (l2 ⊔ l4) lem)
                  ( theory)
                  ( is-fin)))
              ( λ x y →
                ( lower-LEM
                  ( lsuc l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6 ⊔ lsuc l7 ⊔ lsuc l8)
                  ( lem)
                  ( relation-Prop-kripke-model i M* x y)))
              ( λ x n →
                ( lower-LEM
                  ( l2 ⊔ lsuc l3 ⊔ lsuc l5 ⊔ lsuc l6 ⊔ lsuc l7 ⊔ lsuc l8)
                  ( lem)
                  ( valuate-kripke-model i M* n x)))))))

  -- module _
  --   (l6 l7 l8 : Level)
  --   where

    -- private
    --   w' = type-is-small (is-small-equivalence-classes-filtration l6)

    -- extend :
    --   (type-subtype (λ n → theory (var n)) → w' → Prop l8) →
    --   type-Set i → w' → Prop l8
    -- extend f n x
    --   with
    --   lower-LEM
    --   ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
    --   ( lem)
    --   ( theory (var n))
    -- ... | inl in-theory = f (n , in-theory) x
    -- ... | inr _ = raise-empty-Prop l8

    -- is-bounded-valuate-extend :
    --   (f : type-subtype (λ n → theory (var n)) → w' → Prop l8) →
    --   is-bounded-valuate i theory M (extend f)
    -- is-bounded-valuate-extend f n not-in-theory x val
    --   with
    --   lower-LEM
    --   ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
    --   ( lem)
    --   ( theory (var n))
    -- ... | inl in-theory = not-in-theory in-theory
    -- ... | inr not-in-theory' = map-inv-raise val

    -- last :
    --   (w' → w' → Prop l7)
    --   × (type-subtype (λ n → theory (var n)) → w' → Prop l8) →
    --   type-subtype (is-alpha-Prop i theory M {l6} {l7} {l8})
    -- last (r , v) =
    --   pair
    --     ( pair
    --       ( pair
    --         ( pair
    --           ( w')
    --           ( map-is-inhabited
    --             ( λ x →
    --               ( map-equiv-is-small
    --                 ( is-small-equivalence-classes-filtration l6)
    --                 ( class (Φ-equivalence i theory M) x)))
    --             ( is-inhabited-type-kripke-model i M)))
    --         ( r))
    --       ( extend v))
    --     ( unit-trunc-Prop
    --       ( pair
    --         ( equiv-is-small (is-small-equivalence-classes-filtration l6))
    --         ( is-bounded-valuate-extend v)))

    -- is-surjective-last : is-surjective last
    -- is-surjective-last (r , v) =
    --   unit-trunc-Prop
    --     (pair
    --       ( pair
    --         ( λ x y →
    --           ( relation-Prop-kripke-model i r
    --             ( {!   !})
    --             ( {!   !})))
    --         ( {!   !}))
    --       ( {!   !}))

module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} (i : Set l3)
  (C : model-class l1 l2 i l4 l5)
  (filtration : modal-theory l3 i →
                kripke-model l1 l2 i l4 →
                kripke-model l6 l7 i l8)
  where

  filtrate-class :
    model-class l6 l7 i l8
      ( lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5 ⊔ lsuc l6 ⊔ lsuc l7 ⊔ lsuc l8)
  filtrate-class M* =
    ∃-Prop (formula i × type-subtype C)
      ( λ (a , (M , _)) →
        ( M* ＝ filtration (in-list (subformulas-list i a)) M))

  module _
    (filtration-is-filtration :
      ((M , _) : type-subtype C)
      (theory : modal-theory l3 i) →
      is-modal-theory-closed-under-subformulas i theory →
      is-kripke-model-filtration i theory M (filtration theory M))
    where
    filtrate-completeness :
      {l9 : Level} (logic : modal-theory l9 i) →
      completeness logic C →
      completeness logic filtrate-class
    filtrate-completeness logic complete a in-logic =
      complete a
        ( λ M M-in-class x →
          apply-universal-property-trunc-Prop
            ( filtration-is-filtration
              ( M , M-in-class)
              ( in-list (subformulas-list i a))
              ( is-modal-theory-closed-under-subformulas-subformulas-list i a))
            ( (M , x) ⊨ a)
            ( λ is-filt →
              ( backward-implication
                ( kripke-models-filtrations-theorem' i
                  ( in-list (subformulas-list i a))
                  ( is-modal-theory-closed-under-subformulas-subformulas-list
                    ( i)
                    ( a))
                  ( M)
                  ( filtration (in-list (subformulas-list i a)) M)
                  ( is-filt)
                  ( a)
                  ( unit-trunc-Prop (is-head a _))
                  ( x))
                ( in-logic
                  ( filtration (in-list (cons a _)) M)
                  ( intro-∃ (a , (M , M-in-class)) refl)
                  ( map-equiv-is-kripke-model-filtration
                    ( i)
                    ( in-list (subformulas-list i a))
                    ( M)
                    ( filtration (in-list (cons a _)) M)
                    ( is-filt)
                    ( class
                      ( Φ-equivalence i
                        ( in-list (subformulas-list i a))
                        ( M))
                      ( x)))))))

  filtrate-soundness :
    {l9 l10 : Level} (logic : modal-theory l9 i) →
    (C₂ : model-class l6 l7 i l8 l10) →
    ( ((M , _) : type-subtype C) →
      (a : formula i) →
      is-in-subtype C₂ (filtration (in-list (subformulas-list i a)) M)) →
    soundness logic C₂ →
    soundness logic filtrate-class
  filtrate-soundness logic C₂ H sound a in-logic M* in-class =
    apply-universal-property-trunc-Prop
      ( in-class)
      ( M* ⊨M a)
      ( λ ((b , (M , in-C)) , p) →
        ( sound a in-logic M*
          ( tr (is-in-subtype C₂) (inv p) (H (M , in-C) b))))
```

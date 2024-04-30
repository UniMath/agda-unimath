# Kripke models filtrations

```agda
module modal-logic.kripke-models-filtrations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.injective-maps
open import foundation-core.transport-along-identifications

open import modal-logic.axioms
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax

open import univalent-combinatorics.finite-types
```

</details>

## Idea

TODO

## Definition

```agda
-- TODO: move to new file
module _
  {l1 l2 : Level} {A : UU l1}
  where

  data transitive-closure (R : Relation l2 A) : A → A → UU (l1 ⊔ l2)
    where
    base* : {x y : A} → R x y → transitive-closure R x y
    step* :
      {x y z : A} →
      R x y →
      transitive-closure R y z →
      transitive-closure R x z

  transitive-closure-Prop :
    (R : Relation l2 A) → Relation-Prop (l1 ⊔ l2) A
  transitive-closure-Prop R x y =
    trunc-Prop (transitive-closure R x y)

  is-transitive-transitive-closure :
    (R : Relation l2 A) → is-transitive (transitive-closure R)
  is-transitive-transitive-closure R x y z c-yz (base* r-xy) =
    step* r-xy c-yz
  is-transitive-transitive-closure
    R x y z c-yz (step* {y = u} r-xu c-uy) =
      step* r-xu (is-transitive-transitive-closure R u y z c-yz c-uy)

  is-transitive-transitive-closure-Prop :
    (R : Relation l2 A) →
    is-transitive-Relation-Prop (transitive-closure-Prop R)
  is-transitive-transitive-closure-Prop R x y z c-yz c-xy =
    apply-twice-universal-property-trunc-Prop
      ( c-yz)
      ( c-xy)
      ( transitive-closure-Prop R x z)
      ( λ r-yz r-xy →
        ( unit-trunc-Prop (is-transitive-transitive-closure R x y z r-yz r-xy)))

  transitive-closure-preserves-reflexivity :
    (R : Relation l2 A) →
    is-reflexive R →
    is-reflexive (transitive-closure R)
  transitive-closure-preserves-reflexivity R is-refl x = base* (is-refl x)

  transitive-closure-preserves-symmetry :
    (R : Relation l2 A) →
    is-symmetric R →
    is-symmetric (transitive-closure R)
  transitive-closure-preserves-symmetry R is-sym x y (base* r) =
    base* (is-sym x y r)
  transitive-closure-preserves-symmetry R is-sym x y (step* {y = u} r-xu c-uy) =
    is-transitive-transitive-closure R y u x
      ( base* (is-sym x u r-xu))
      ( transitive-closure-preserves-symmetry R is-sym u y c-uy)

  transitive-closure-Prop-preserves-reflexivity :
    (R : Relation l2 A) →
    is-reflexive R →
    is-reflexive-Relation-Prop (transitive-closure-Prop R)
  transitive-closure-Prop-preserves-reflexivity R is-refl x =
    unit-trunc-Prop (transitive-closure-preserves-reflexivity R is-refl x)

  transitive-closure-Prop-preserves-symmetry :
    (R : Relation l2 A) →
    is-symmetric R →
    is-symmetric-Relation-Prop (transitive-closure-Prop R)
  transitive-closure-Prop-preserves-symmetry R is-sym x y =
    map-universal-property-trunc-Prop
      ( transitive-closure-Prop R y x)
      ( unit-trunc-Prop ∘ transitive-closure-preserves-symmetry R is-sym x y)

module _
  {l1 : Level} (i : Set l1)
  where

  module _
    {l2 : Level} (theory : modal-theory l2 i)
    where

    is-modal-theory-has-subformulas-Prop : formula i → Prop l2
    is-modal-theory-has-subformulas-Prop (var _) = raise-unit-Prop l2
    is-modal-theory-has-subformulas-Prop ⊥ = raise-unit-Prop l2
    is-modal-theory-has-subformulas-Prop (a →ₘ b) =
      product-Prop (theory a) (theory b)
    is-modal-theory-has-subformulas-Prop (□ a) = theory a

    is-modal-theory-has-subformulas : formula i → UU l2
    is-modal-theory-has-subformulas =
      type-Prop ∘ is-modal-theory-has-subformulas-Prop

    is-modal-theory-closed-under-subformulas-Prop : Prop (l1 ⊔ l2)
    is-modal-theory-closed-under-subformulas-Prop =
      implicit-Π-Prop
        ( formula i)
        ( λ a →
          ( function-Prop
            ( is-in-subtype theory a)
            ( is-modal-theory-has-subformulas-Prop a)))

    is-modal-theory-closed-under-subformulas : UU (l1 ⊔ l2)
    is-modal-theory-closed-under-subformulas =
      type-Prop (is-modal-theory-closed-under-subformulas-Prop)

    is-modal-theory-closed-under-subformulas-condition :
      ( {a b : formula i} →
        is-in-subtype theory (a →ₘ b) →
        is-in-subtype theory a × is-in-subtype theory b) →
      ( {a : formula i} → is-in-subtype theory (□ a) → is-in-subtype theory a) →
      is-modal-theory-closed-under-subformulas
    is-modal-theory-closed-under-subformulas-condition
      h-impl h-box {var n} _ = raise-star
    is-modal-theory-closed-under-subformulas-condition
      h-impl h-box {⊥} _ = raise-star
    is-modal-theory-closed-under-subformulas-condition
      h-impl h-box {a →ₘ b} = h-impl
    is-modal-theory-closed-under-subformulas-condition
      h-impl h-box {□ a} = h-box

module _
  {l1 l2 l3 l4 l5 : Level} (i : Set l3)
  (theory : modal-theory l5 i)
  (M : kripke-model l1 l2 i l4)
  where

  Φ-equivalence :
    equivalence-relation (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5) (type-kripke-model i M)
  pr1 Φ-equivalence x y =
    Π-Prop
      ( formula i)
      ( λ a →
        ( function-Prop
          ( is-in-subtype theory a)
          ( iff-Prop ((M , x) ⊨ a) ((M , y) ⊨ a))))
  pr1 (pr2 Φ-equivalence) x a in-theory = id , id
  pr1 (pr2 (pr2 Φ-equivalence)) x y r a in-theory =
    inv-iff (r a in-theory)
  pr2 (pr2 (pr2 Φ-equivalence)) x y z r-xy r-yz a in-theory =
    r-xy a in-theory ∘iff r-yz a in-theory

  valuate-function-equivalence-class :
    equivalence-class Φ-equivalence →
    UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5)
  valuate-function-equivalence-class class =
    Σ ( type-subtype theory → Prop (l1 ⊔ l2 ⊔ l4))
      ( λ f →
        ( (a , in-theory) : type-subtype theory)
        ( (x , _) :
            type-subtype (subtype-equivalence-class Φ-equivalence class)) →
            f (a , in-theory) ⇔ ((M , x) ⊨ a))

  is-prop-valuate-function-equivalence-class :
    (class : equivalence-class Φ-equivalence) →
    is-prop (valuate-function-equivalence-class class)
  is-prop-valuate-function-equivalence-class class =
    apply-universal-property-trunc-Prop
      ( is-inhabited-subtype-equivalence-class Φ-equivalence class)
      ( is-prop _ , is-prop-is-prop _)
      ( λ x →
        ( is-prop-all-elements-equal
          ( λ (f , f-val) (g , g-val) →
            ( eq-pair-Σ
              ( eq-htpy
                ( λ a →
                  ( eq-iff
                    ( λ fa →
                      ( backward-implication
                        ( g-val a x)
                        ( forward-implication (f-val a x) fa)))
                    ( λ ga →
                      ( backward-implication
                        ( f-val a x)
                        ( forward-implication (g-val a x) ga))))))
              ( eq-is-prop
                ( is-prop-Π
                  ( λ (a , in-theory) →
                    ( is-prop-Π
                      ( λ (x , _) →
                        ( is-prop-iff-Prop
                          ( g (a , in-theory))
                          ( (M , x) ⊨ a)))))))))))

  function-equivalence-class :
    (class : equivalence-class Φ-equivalence) →
    valuate-function-equivalence-class class
  function-equivalence-class class =
    apply-universal-property-trunc-Prop
      ( is-inhabited-subtype-equivalence-class Φ-equivalence class)
      ( pair
        ( valuate-function-equivalence-class class)
        ( is-prop-valuate-function-equivalence-class class))
      ( λ (x , x-in-class) →
        ( pair
          ( λ (a , _) → (M , x) ⊨ a)
          ( λ (a , in-theory) (y , y-in-class) →
            ( apply-effectiveness-class Φ-equivalence {x} {y}
              ( concat
                ( eq-effective-quotient' Φ-equivalence x class x-in-class)
                ( _)
                ( inv
                  ( eq-effective-quotient' Φ-equivalence y class y-in-class)))
              ( a)
              ( in-theory)))))

  map-function-equivalence-class :
    equivalence-class Φ-equivalence →
    type-subtype theory → Prop (l1 ⊔ l2 ⊔ l4)
  map-function-equivalence-class = pr1 ∘ function-equivalence-class

  is-injective-map-function-equivalence-class :
    is-injective map-function-equivalence-class
  is-injective-map-function-equivalence-class {x-class} {y-class} p =
    let (f , f-val) = function-equivalence-class x-class
        (g , g-val) = function-equivalence-class y-class
    in apply-twice-universal-property-trunc-Prop
      ( is-inhabited-subtype-equivalence-class Φ-equivalence x-class)
      ( is-inhabited-subtype-equivalence-class Φ-equivalence y-class)
      ( pair
        ( x-class ＝ y-class)
        ( is-set-equivalence-class Φ-equivalence x-class y-class))
      ( λ (x , x-in-class) (y , y-in-class) →
        ( equational-reasoning
            x-class ＝ class Φ-equivalence x by
                        ( inv
                          ( eq-class-equivalence-class
                            ( Φ-equivalence)
                            ( x-class)
                            ( x-in-class)))
                    ＝ class Φ-equivalence y by
                        ( apply-effectiveness-class'
                          ( Φ-equivalence)
                          ( λ a a-in-theory →
                            ( g-val (a , a-in-theory) (y , y-in-class)
                              ∘iff iff-eq (htpy-eq p (a , a-in-theory))
                              ∘iff inv-iff
                                    ( f-val
                                      ( a , a-in-theory)
                                      ( x , x-in-class)))))
                    ＝ y-class by
                        ( eq-class-equivalence-class
                          ( Φ-equivalence)
                          ( y-class)
                          ( y-in-class))))

  injection-map-function-equivalence-class :
    injection
      ( equivalence-class Φ-equivalence)
      ( type-subtype theory → Prop (l1 ⊔ l2 ⊔ l4))
  pr1 injection-map-function-equivalence-class =
    map-function-equivalence-class
  pr2 injection-map-function-equivalence-class =
    is-injective-map-function-equivalence-class

  module _
    {l6 l7 l8 : Level} (M* : kripke-model l6 l7 i l8)
    where

    is-filtration-valuate-Prop :
      equivalence-class Φ-equivalence ≃ type-kripke-model i M* →
      Prop (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l8)
    is-filtration-valuate-Prop e =
      Π-Prop (type-Set i)
        ( λ n →
          ( Π-Prop (type-kripke-model i M)
            ( λ x → iff-Prop
              ( product-Prop (theory (var n)) (valuate-kripke-model i M n x))
              ( valuate-kripke-model i M* n
                ( map-equiv e (class Φ-equivalence x))))))

    is-filtration-valuate :
      equivalence-class Φ-equivalence ≃ type-kripke-model i M* →
      UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l8)
    is-filtration-valuate = type-Prop ∘ is-filtration-valuate-Prop

    filtration-relation-lower-bound-Prop :
      equivalence-class Φ-equivalence ≃ type-kripke-model i M* →
      Prop (l1 ⊔ l2 ⊔ l7)
    filtration-relation-lower-bound-Prop e =
      Π-Prop (type-kripke-model i M)
        ( λ x →
          ( Π-Prop (type-kripke-model i M)
            ( λ y →
              ( function-Prop (relation-kripke-model i M x y)
                ( relation-Prop-kripke-model i M*
                  ( map-equiv e (class Φ-equivalence x))
                  ( map-equiv e (class Φ-equivalence y)))))))

    filtration-relation-lower-bound :
      equivalence-class Φ-equivalence ≃ type-kripke-model i M* →
      UU (l1 ⊔ l2 ⊔ l7)
    filtration-relation-lower-bound =
      type-Prop ∘ filtration-relation-lower-bound-Prop

    filtration-relation-upper-bound-Prop :
      equivalence-class Φ-equivalence ≃ type-kripke-model i M* →
      Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l7)
    filtration-relation-upper-bound-Prop e =
      Π-Prop (formula i)
        ( λ a →
          ( function-Prop (is-in-subtype theory (□ a))
            ( Π-Prop (type-kripke-model i M)
              ( λ x →
                ( Π-Prop (type-kripke-model i M)
                  ( λ y →
                    ( function-Prop
                      ( relation-kripke-model i M*
                        ( map-equiv e (class Φ-equivalence x))
                        ( map-equiv e (class Φ-equivalence y)))
                      ( hom-Prop ((M , x) ⊨ □ a)
                        ( (M , y) ⊨ a)))))))))

    filtration-relation-upper-bound :
      equivalence-class Φ-equivalence ≃ type-kripke-model i M* →
      UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l7)
    filtration-relation-upper-bound =
      type-Prop ∘ filtration-relation-upper-bound-Prop

    -- is-alpha-Σ :
    --   UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ l6 ⊔ l8)
    -- is-alpha-Σ =
    --   product
    --     ( equivalence-class Φ-equivalence ≃ type-kripke-model i M*)
    --     ( is-bounded-valuate (valuate-kripke-model i M*))

    -- is-alpha-Prop :
    --   Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ l6 ⊔ l8)
    -- is-alpha-Prop = trunc-Prop is-alpha-Σ

    is-kripke-model-filtration-Σ :
      UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ l6 ⊔ l7 ⊔ l8)
    is-kripke-model-filtration-Σ =
      Σ ( equivalence-class Φ-equivalence ≃ type-kripke-model i M*)
        ( λ e →
          ( product
            ( is-filtration-valuate e)
            ( product
              ( filtration-relation-lower-bound e)
              ( filtration-relation-upper-bound e))))

    is-kripke-model-filtration-Prop :
      Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ l6 ⊔ l7 ⊔ l8)
    is-kripke-model-filtration-Prop = trunc-Prop is-kripke-model-filtration-Σ

    is-kripke-model-filtration :
      UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ l6 ⊔ l7 ⊔ l8)
    is-kripke-model-filtration = type-Prop is-kripke-model-filtration-Prop

    equiv-is-kripke-model-filtration :
      is-kripke-model-filtration-Σ →
      equivalence-class Φ-equivalence ≃ type-kripke-model i M*
    equiv-is-kripke-model-filtration = pr1

    map-equiv-is-kripke-model-filtration :
      is-kripke-model-filtration-Σ →
      equivalence-class Φ-equivalence → type-kripke-model i M*
    map-equiv-is-kripke-model-filtration =
      map-equiv ∘ equiv-is-kripke-model-filtration

    map-inv-equiv-is-kripke-model-filtration :
      is-kripke-model-filtration-Σ →
      type-kripke-model i M* → equivalence-class Φ-equivalence
    map-inv-equiv-is-kripke-model-filtration =
      map-inv-equiv ∘ equiv-is-kripke-model-filtration

    is-filtration-valuate-is-kripke-model-filtration :
      (e : is-kripke-model-filtration-Σ) →
      is-filtration-valuate (equiv-is-kripke-model-filtration e)
    is-filtration-valuate-is-kripke-model-filtration = pr1 ∘ pr2

    filtration-relation-lower-bound-is-kripke-model-filtration :
      (e : is-kripke-model-filtration-Σ) →
      filtration-relation-lower-bound (equiv-is-kripke-model-filtration e)
    filtration-relation-lower-bound-is-kripke-model-filtration =
      pr1 ∘ pr2 ∘ pr2

    filtration-relation-upper-bound-is-kripke-model-filtration :
      (e : is-kripke-model-filtration-Σ) →
      filtration-relation-upper-bound (equiv-is-kripke-model-filtration e)
    filtration-relation-upper-bound-is-kripke-model-filtration =
      pr2 ∘ pr2 ∘ pr2

    class-x-eq-x*' :
      (e : equivalence-class Φ-equivalence ≃ type-kripke-model i M*) →
      (x : type-kripke-model i M)
      (x* : type-kripke-model i M*) →
      is-in-equivalence-class Φ-equivalence (map-inv-equiv e x*) x →
      map-equiv e (class Φ-equivalence x) ＝ x*
    class-x-eq-x*' e x x* x-in-x* =
      concat
        ( ap
          ( map-equiv e)
          ( eq-class-equivalence-class Φ-equivalence
            ( map-inv-equiv e x*)
            ( x-in-x*)))
        ( x*)
        ( is-section-map-section-map-equiv e x*)

    class-x-eq-x* :
      (is-filt : is-kripke-model-filtration-Σ)
      (x : type-kripke-model i M)
      (x* : type-kripke-model i M*) →
      is-in-equivalence-class Φ-equivalence
        ( map-inv-equiv-is-kripke-model-filtration is-filt x*) x →
      map-equiv-is-kripke-model-filtration is-filt (class Φ-equivalence x) ＝ x*
    class-x-eq-x* = class-x-eq-x*' ∘ equiv-is-kripke-model-filtration

    filtration-relation-preserves-reflexivity :
      (e : equivalence-class Φ-equivalence ≃ type-kripke-model i M*) →
      type-Prop (filtration-relation-lower-bound-Prop e) →
      is-in-subtype (reflexive-kripke-class l1 l2 i l4) M →
      is-in-subtype (reflexive-kripke-class l6 l7 i l8) M*
    filtration-relation-preserves-reflexivity e bound is-refl x* =
      apply-universal-property-trunc-Prop
        ( is-inhabited-subtype-equivalence-class Φ-equivalence
          ( map-inv-equiv e x*))
        ( relation-Prop-kripke-model i M* x* x*)
        ( λ (x , x-in-x*) →
          ( tr
            ( λ y → relation-kripke-model i M* y y)
            ( class-x-eq-x*' e x x* x-in-x*)
            ( bound x x (is-refl x))))

    filtration-preserves-reflexivity :
      is-kripke-model-filtration →
      is-in-subtype (reflexive-kripke-class l1 l2 i l4) M →
      is-in-subtype (reflexive-kripke-class l6 l7 i l8) M*
    filtration-preserves-reflexivity t-is-filt is-refl class =
      apply-universal-property-trunc-Prop
        ( t-is-filt)
        ( relation-Prop-kripke-model i M* class class)
        ( λ is-filt →
          ( apply-universal-property-trunc-Prop
            ( is-inhabited-subtype-equivalence-class Φ-equivalence
              ( map-inv-equiv-is-kripke-model-filtration is-filt class))
            ( relation-Prop-kripke-model i M* class class)
            ( λ (x , in-class) →
              ( tr
                ( λ y → relation-kripke-model i M* y y)
                ( class-x-eq-x* is-filt x class in-class)
                ( filtration-relation-lower-bound-is-kripke-model-filtration
                  ( is-filt)
                  ( x)
                  ( x)
                  ( is-refl x))))))

  is-inhabited-equivalence-classes :
    is-inhabited (equivalence-class Φ-equivalence)
  is-inhabited-equivalence-classes =
    map-is-inhabited
      ( class Φ-equivalence)
      ( is-inhabited-type-kripke-model i M)

  minimal-kripke-model-filtration-relation :
    Relation-Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5) (equivalence-class Φ-equivalence)
  minimal-kripke-model-filtration-relation x* y* =
    ∃-Prop
      ( type-kripke-model i M × type-kripke-model i M)
      ( λ (x , y) →
        ( product
          ( relation-kripke-model i M x y)
          ( product
            ( is-in-equivalence-class Φ-equivalence x* x)
            ( is-in-equivalence-class Φ-equivalence y* y))))

  minimal-kripke-model-filtration-valuate :
    type-Set i →
    equivalence-class Φ-equivalence →
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  minimal-kripke-model-filtration-valuate n x* =
    product-Prop
      ( theory (var n))
      ( Π-Prop
        ( type-kripke-model i M)
        ( λ x →
          ( function-Prop
            ( is-in-equivalence-class Φ-equivalence x* x)
            ( valuate-kripke-model i M n x))))

  minimal-kripke-model-filtration :
    kripke-model
      ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
      ( i)
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  pr1 (pr1 (pr1 minimal-kripke-model-filtration)) =
    equivalence-class Φ-equivalence
  pr2 (pr1 (pr1 minimal-kripke-model-filtration)) =
    is-inhabited-equivalence-classes
  pr2 (pr1 minimal-kripke-model-filtration) =
    minimal-kripke-model-filtration-relation
  pr2 minimal-kripke-model-filtration =
    minimal-kripke-model-filtration-valuate

  minimal-transitive-kripke-model-filtration :
    kripke-model
      ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
      ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
      ( i)
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  pr1 (pr1 (pr1 minimal-transitive-kripke-model-filtration)) =
    equivalence-class Φ-equivalence
  pr2 (pr1 (pr1 minimal-transitive-kripke-model-filtration)) =
    is-inhabited-equivalence-classes
  pr2 (pr1 minimal-transitive-kripke-model-filtration) =
    transitive-closure-Prop
      ( type-Relation-Prop minimal-kripke-model-filtration-relation)
  pr2 minimal-transitive-kripke-model-filtration =
    minimal-kripke-model-filtration-valuate

  module _
    (theory-is-closed : is-modal-theory-closed-under-subformulas i theory)
    where

    proof-upper-bound :
      (a : formula i) →
      is-in-subtype theory (□ a) →
      (x y : type-kripke-model i M) →
      relation-kripke-model i minimal-kripke-model-filtration
        ( class Φ-equivalence x)
        ( class Φ-equivalence y) →
      type-Prop ((M , x) ⊨ □ a) →
      type-Prop ((M , y) ⊨ a)
    proof-upper-bound a box-in-theory x y r-xy x-forces-box =
      apply-universal-property-trunc-Prop
        ( r-xy)
        ( (M , y) ⊨ a)
        ( λ ((x' , y') , r-xy' , iff-x , iff-y) →
          ( backward-implication
            ( iff-y a (theory-is-closed box-in-theory))
            ( forward-implication
              ( iff-x (□ a) box-in-theory)
              ( x-forces-box)
              ( y')
              ( r-xy'))))

    proof-lower-bound :
      (x y : type-kripke-model i M) →
      relation-kripke-model i M x y →
      type-Prop
        ( minimal-kripke-model-filtration-relation
          ( class Φ-equivalence x)
          ( class Φ-equivalence y))
    proof-lower-bound x y r =
      intro-∃ (x , y) (r , (λ _ _ → id , id) , (λ _ _ → id , id))

    is-kripke-model-filtration-minimal-kripke-model-filtration :
      is-kripke-model-filtration minimal-kripke-model-filtration
    is-kripke-model-filtration-minimal-kripke-model-filtration =
      intro-∃
        ( id-equiv)
        ( triple
          ( λ n x →
            ( pair
              ( λ (in-theory , val-n) →
                ( pair in-theory
                  ( λ y eq-xy →
                    ( map-inv-raise
                      ( forward-implication
                        ( eq-xy (var n) in-theory)
                        ( map-raise val-n)))))))
            ( λ (in-theory , val-n) → in-theory , val-n x (λ _ _ → id , id)))
          ( proof-lower-bound)
          ( proof-upper-bound))

    helper :
      is-in-subtype (transitivity-kripke-class l1 l2 i l4) M →
      (a : formula i) →
      is-in-subtype theory (□ a) →
      (x y : type-kripke-model i M) →
      transitive-closure
        ( relation-kripke-model i minimal-kripke-model-filtration)
        ( class Φ-equivalence x)
        ( class Φ-equivalence y) →
      type-Prop ((M , x) ⊨ □ a) →
      type-Prop ((M , y) ⊨ a)
    helper M-is-trans a box-in-theory x y (base* r-xy) x-forces-box =
      proof-upper-bound a box-in-theory x y r-xy x-forces-box
    helper M-is-trans a box-in-theory x y (step* {y = z*} r-xz c-zy)
      x-forces-box =
        apply-universal-property-trunc-Prop
          ( is-inhabited-subtype-equivalence-class Φ-equivalence z*)
          ( (M , y) ⊨ a)
          ( λ (z , z-in-z*) →
            aux z (eq-class-equivalence-class Φ-equivalence z* z-in-z*))
      where
      aux :
        (z : type-kripke-model i M) →
        class Φ-equivalence z ＝ z* →
        type-Prop ((M , y) ⊨ a)
      aux z refl =
        apply-universal-property-trunc-Prop
          ( r-xz)
          ( (M , y) ⊨ a)
          ( λ ((x' , z') , r-xz' , iff-x , iff-z) →
            ( helper M-is-trans a box-in-theory z y c-zy
              ( backward-implication
                ( iff-z (□ a) box-in-theory)
                ( ax-4-soundness i l2 l4 (□ a →ₘ □ □ a) (a , refl) M M-is-trans
                  ( x')
                  ( forward-implication
                    ( iff-x (□ a) box-in-theory)
                    ( x-forces-box))
                  ( z')
                  ( r-xz')))))

    filtration-relation-upper-bound-Prop-minimal-transitive-kripke-model-filtration :
      is-in-subtype (transitivity-kripke-class l1 l2 i l4) M →
      filtration-relation-upper-bound
        minimal-transitive-kripke-model-filtration id-equiv
    filtration-relation-upper-bound-Prop-minimal-transitive-kripke-model-filtration
      M-is-trans a box-in-theory x y r-xy x-forces-box =
        apply-universal-property-trunc-Prop
          ( r-xy)
          ( (M , y) ⊨ a)
          ( λ r → helper M-is-trans a box-in-theory x y r x-forces-box)

    is-kripke-model-filtration-minimal-transitive-kripke-model-filtration :
      is-in-subtype (transitivity-kripke-class l1 l2 i l4) M →
      is-kripke-model-filtration minimal-transitive-kripke-model-filtration
    is-kripke-model-filtration-minimal-transitive-kripke-model-filtration
      M-is-trans =
        intro-∃
          ( id-equiv)
          ( triple
            ( λ n x →
              ( pair
                ( λ (in-theory , val-n) →
                  ( pair in-theory
                    ( λ y eq-xy →
                      ( map-inv-raise
                        ( forward-implication
                          ( eq-xy (var n) in-theory)
                          ( map-raise val-n)))))))
              ( λ (in-theory , val-n) → in-theory , val-n x (λ _ _ → id , id)))
            ( λ x y r → unit-trunc-Prop (base* (proof-lower-bound x y r)))
            ( filtration-relation-upper-bound-Prop-minimal-transitive-kripke-model-filtration
              ( M-is-trans)))

    minimal-filtration-preserves-reflexivity :
      is-in-subtype (reflexive-kripke-class l1 l2 i l4) M →
      is-in-subtype
        ( reflexive-kripke-class
          ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-kripke-model-filtration)
    minimal-filtration-preserves-reflexivity =
      filtration-preserves-reflexivity
        ( minimal-kripke-model-filtration)
        ( is-kripke-model-filtration-minimal-kripke-model-filtration)

    minimal-kripke-model-filtration-relation-preserves-symmetry :
      is-in-subtype (symmetry-kripke-class l1 l2 i l4) M →
      is-symmetric-Relation-Prop minimal-kripke-model-filtration-relation
    minimal-kripke-model-filtration-relation-preserves-symmetry is-sym x* y* =
      map-universal-property-trunc-Prop
        ( relation-Prop-kripke-model i minimal-kripke-model-filtration y* x*)
        ( λ ((x , y) , r-xy , x-in-x* , y-in-y*) →
          ( intro-∃ (y , x) (is-sym x y r-xy , y-in-y* , x-in-x*)))

    minimal-filtration-preserves-symmetry :
      is-in-subtype (symmetry-kripke-class l1 l2 i l4) M →
      is-in-subtype
        ( symmetry-kripke-class
          ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-kripke-model-filtration)
    minimal-filtration-preserves-symmetry =
      minimal-kripke-model-filtration-relation-preserves-symmetry

    minimal-transitive-filtration-preserves-reflexivity :
      is-in-subtype (reflexive-kripke-class l1 l2 i l4) M →
      is-in-subtype
        ( reflexive-kripke-class
          ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
          ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-transitive-kripke-model-filtration)
    minimal-transitive-filtration-preserves-reflexivity is-refl =
      transitive-closure-Prop-preserves-reflexivity
        ( type-Relation-Prop minimal-kripke-model-filtration-relation)
        ( minimal-filtration-preserves-reflexivity is-refl)

    minimal-transitive-kripke-model-filtration-preserves-symmetry :
      is-in-subtype (symmetry-kripke-class l1 l2 i l4) M →
      is-in-subtype
        ( symmetry-kripke-class
          ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
          ( lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-transitive-kripke-model-filtration)
    minimal-transitive-kripke-model-filtration-preserves-symmetry is-sym =
      transitive-closure-Prop-preserves-symmetry
        ( type-Relation-Prop minimal-kripke-model-filtration-relation)
        ( minimal-filtration-preserves-symmetry is-sym)

    minimal-transitive-kripke-model-filtration-is-transitive :
      is-in-subtype
        ( transitivity-kripke-class
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-transitive-kripke-model-filtration)
    minimal-transitive-kripke-model-filtration-is-transitive =
      is-transitive-transitive-closure-Prop
        ( type-Relation-Prop minimal-kripke-model-filtration-relation)

    minimal-transitive-filtration-preserves-equivalence :
      is-in-subtype (equivalence-kripke-class l1 l2 i l4) M →
      is-in-subtype
        ( equivalence-kripke-class
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-transitive-kripke-model-filtration)
    minimal-transitive-filtration-preserves-equivalence
      (is-refl , is-sym , _) =
        triple
          ( minimal-transitive-filtration-preserves-reflexivity is-refl)
          ( minimal-transitive-kripke-model-filtration-preserves-symmetry
            ( is-sym))
          ( minimal-transitive-kripke-model-filtration-is-transitive)

module _
  (l1 l2 : Level)
  {l3 : Level} (i : Set l3)
  (l4 : Level)
  (l5 l6 l7 l8 : Level)
  where
  filtration-models :
    model-class l1 l2 i l4
      (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6 ⊔ lsuc l7 ⊔ lsuc l8)
  filtration-models M* =
    ∃-Prop
      ( modal-theory l5 i × kripke-model l6 l7 i l8)
      ( λ (theory , M) →
        ( product
          ( is-finite (type-subtype theory))
          ( is-kripke-model-filtration i theory M M*)))
```

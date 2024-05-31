# Kripke models filtrations

```agda
module modal-logic.kripke-models-filtrations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications

open import modal-logic.axioms
open import modal-logic.closed-under-subformulas-theories
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.kripke-semantics

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.subfinite-types
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {i : Set l3}
  (theory : modal-theory l5 i)
  (M : kripke-model l1 l2 i l4)
  where

  Φ-equivalence :
    equivalence-relation (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5) (type-kripke-model i M)
  pr1 Φ-equivalence x y =
    Π-Prop
      ( modal-formula i)
      ( λ a →
        ( function-Prop
          ( is-in-subtype theory a)
          ( (M , x) ⊨ₘ a ⇔ (M , y) ⊨ₘ a)))
  pr1 (pr2 Φ-equivalence) x a in-theory = id , id
  pr1 (pr2 (pr2 Φ-equivalence)) x y r a in-theory =
    inv-iff (r a in-theory)
  pr2 (pr2 (pr2 Φ-equivalence)) x y z r-xy r-yz a in-theory =
    r-xy a in-theory ∘iff r-yz a in-theory

  map-function-equivalence-class-Set :
    Set (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l4 ⊔ l5)
  map-function-equivalence-class-Set =
    function-Set (type-subtype theory) (Prop-Set (l1 ⊔ l2 ⊔ l4))

  map-function-worlds :
    type-kripke-model i M → type-Set map-function-equivalence-class-Set
  map-function-worlds x (a , _) = (M , x) ⊨ₘ a

  map-function-worlds-correct :
    (x y : type-kripke-model i M) →
    sim-equivalence-relation Φ-equivalence x y →
    map-function-worlds x ＝ map-function-worlds y
  map-function-worlds-correct x y s =
    eq-htpy
      ( λ (a , a-in-theory) →
        ( eq-iff' ((M , x) ⊨ₘ a) ((M , y) ⊨ₘ a) (s a a-in-theory)))

  map-function-equivalence-class :
    equivalence-class Φ-equivalence →
    type-subtype theory → Prop (l1 ⊔ l2 ⊔ l4)
  map-function-equivalence-class =
    rec-equivalence-class Φ-equivalence
      ( map-function-equivalence-class-Set)
      ( map-function-worlds)
      ( map-function-worlds-correct)

  is-injective-map-function-equivalence-class :
    is-injective map-function-equivalence-class
  is-injective-map-function-equivalence-class {x-class} {y-class} p =
    apply-twice-universal-property-trunc-Prop
      ( is-inhabited-subtype-equivalence-class Φ-equivalence x-class)
      ( is-inhabited-subtype-equivalence-class Φ-equivalence y-class)
      ( pair
        ( x-class ＝ y-class)
        ( is-set-equivalence-class Φ-equivalence x-class y-class))
      ( λ (x , x-in-class) (y , y-in-class) →
        ( eq-share-common-element-equivalence-class Φ-equivalence
          ( x-class)
          ( y-class)
          ( intro-exists x
            ( pair
              ( x-in-class)
              ( transitive-is-in-equivalence-class Φ-equivalence
                ( y-class)
                ( y)
                ( x)
                ( y-in-class)
                ( λ a a-in-theory →
                  ( iff-eq
                    ( inv
                      ( ap (λ f → f (a , a-in-theory))
                        ( equational-reasoning
                            map-function-worlds x
                              ＝ map-function-equivalence-class x-class
                                by
                                  inv
                                    ( compute-rec-equivalence-class'
                                      ( Φ-equivalence)
                                      ( map-function-equivalence-class-Set)
                                      ( map-function-worlds)
                                      ( map-function-worlds-correct)
                                      ( x-class)
                                      ( x)
                                      ( x-in-class))
                              ＝ map-function-equivalence-class y-class
                                by p
                              ＝ map-function-worlds y
                                by
                                  compute-rec-equivalence-class'
                                    ( Φ-equivalence)
                                    ( map-function-equivalence-class-Set)
                                    ( map-function-worlds)
                                    ( map-function-worlds-correct)
                                    ( y-class)
                                    ( y)
                                    ( y-in-class)))))))))))

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
          ( theory (varₘ n) ⇒
            ( Π-Prop (type-kripke-model i M)
              ( λ x → iff-Prop
                ( valuate-kripke-model i M n x)
                ( valuate-kripke-model i M* n
                  ( map-equiv e (class Φ-equivalence x)))))))

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
      Π-Prop (modal-formula i)
        ( λ a →
          ( function-Prop (is-in-subtype theory (□ₘ a))
            ( Π-Prop (type-kripke-model i M)
              ( λ x →
                ( Π-Prop (type-kripke-model i M)
                  ( λ y →
                    ( function-Prop
                      ( relation-kripke-model i M*
                        ( map-equiv e (class Φ-equivalence x))
                        ( map-equiv e (class Φ-equivalence y)))
                      ( (M , x) ⊨ₘ □ₘ a ⇒ (M , y) ⊨ₘ a))))))))

    filtration-relation-upper-bound :
      equivalence-class Φ-equivalence ≃ type-kripke-model i M* →
      UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l7)
    filtration-relation-upper-bound =
      type-Prop ∘ filtration-relation-upper-bound-Prop

    is-kripke-model-filtration :
      UU (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5) ⊔ l6 ⊔ l7 ⊔ l8)
    is-kripke-model-filtration =
      Σ ( equivalence-class Φ-equivalence ≃ type-kripke-model i M*)
        ( λ e →
          ( product
            ( is-filtration-valuate e)
            ( product
              ( filtration-relation-lower-bound e)
              ( filtration-relation-upper-bound e))))

    equiv-is-kripke-model-filtration :
      is-kripke-model-filtration →
      equivalence-class Φ-equivalence ≃ type-kripke-model i M*
    equiv-is-kripke-model-filtration = pr1

    map-equiv-is-kripke-model-filtration :
      is-kripke-model-filtration →
      equivalence-class Φ-equivalence → type-kripke-model i M*
    map-equiv-is-kripke-model-filtration =
      map-equiv ∘ equiv-is-kripke-model-filtration

    map-inv-equiv-is-kripke-model-filtration :
      is-kripke-model-filtration →
      type-kripke-model i M* → equivalence-class Φ-equivalence
    map-inv-equiv-is-kripke-model-filtration =
      map-inv-equiv ∘ equiv-is-kripke-model-filtration

    is-filtration-valuate-is-kripke-model-filtration :
      (e : is-kripke-model-filtration) →
      is-filtration-valuate (equiv-is-kripke-model-filtration e)
    is-filtration-valuate-is-kripke-model-filtration = pr1 ∘ pr2

    filtration-relation-lower-bound-is-kripke-model-filtration :
      (e : is-kripke-model-filtration) →
      filtration-relation-lower-bound (equiv-is-kripke-model-filtration e)
    filtration-relation-lower-bound-is-kripke-model-filtration =
      pr1 ∘ pr2 ∘ pr2

    filtration-relation-upper-bound-is-kripke-model-filtration :
      (e : is-kripke-model-filtration) →
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
      (is-filt : is-kripke-model-filtration)
      (x : type-kripke-model i M)
      (x* : type-kripke-model i M*) →
      is-in-equivalence-class Φ-equivalence
        ( map-inv-equiv-is-kripke-model-filtration is-filt x*) x →
      map-equiv-is-kripke-model-filtration is-filt (class Φ-equivalence x) ＝ x*
    class-x-eq-x* = class-x-eq-x*' ∘ equiv-is-kripke-model-filtration

    filtration-relation-preserves-reflexivity :
      (e : equivalence-class Φ-equivalence ≃ type-kripke-model i M*) →
      type-Prop (filtration-relation-lower-bound-Prop e) →
      is-in-subtype (reflexive-kripke-models l1 l2 i l4) M →
      is-in-subtype (reflexive-kripke-models l6 l7 i l8) M*
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
      is-in-subtype (reflexive-kripke-models l1 l2 i l4) M →
      is-in-subtype (reflexive-kripke-models l6 l7 i l8) M*
    filtration-preserves-reflexivity is-filt is-refl class =
      apply-universal-property-trunc-Prop
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
              ( is-refl x))))

module _
  {l1 l2 l3 l4 l5 : Level} (i : Set l3)
  (M : kripke-model l1 l2 i l4)
  (lem : LEM (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)))
  (theory : modal-theory l5 i)
  (is-fin : is-finite (type-subtype theory))
  where

  is-finite-equivalence-classes-filtration :
    is-finite (equivalence-class (Φ-equivalence theory M))
  is-finite-equivalence-classes-filtration =
    is-finite-injection lem
      ( injection-map-function-equivalence-class theory M)
      ( is-finite-function-type is-fin (is-finite-Prop-LEM (lower-LEM _ lem)))
```

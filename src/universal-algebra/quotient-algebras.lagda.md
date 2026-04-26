# Quotient algebras

```agda
module universal-algebra.quotient-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.finite-sequences-set-quotients
open import foundation.functoriality-propositional-truncation
open import foundation.multivariable-functoriality-set-quotients
open import foundation.multivariable-operations
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.congruences
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

The
{{#concept "quotient" Disambiguation="of an algebra of an algebraic theory, single-sorted, finitary" WD="quotient algebra" WDID=Q2589508}}
of an [algebra](universal-algebra.algebras.md) by a
[congruence](universal-algebra.congruences.md) is the
[set quotient](foundation.set-quotients.md) by that congruence. This quotient
again has the structure of an algebra inherited by the original one.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R : congruence-Algebra l4 σ T A)
  where

  set-quotient-Algebra : Set (l3 ⊔ l4)
  set-quotient-Algebra =
    quotient-Set (equivalence-relation-congruence-Algebra σ T A R)

  type-quotient-Algebra : UU (l3 ⊔ l4)
  type-quotient-Algebra = pr1 set-quotient-Algebra

  is-set-set-quotient-Algebra : is-set type-quotient-Algebra
  is-set-set-quotient-Algebra = pr2 set-quotient-Algebra

  compute-quotient-Algebra :
    equivalence-class
      ( equivalence-relation-congruence-Algebra σ T A R) ≃
    type-quotient-Algebra
  compute-quotient-Algebra =
    compute-set-quotient
      ( equivalence-relation-congruence-Algebra σ T A R)

  set-quotient-equivalence-class-Algebra :
    equivalence-class
      ( equivalence-relation-congruence-Algebra σ T A R) →
    type-quotient-Algebra
  set-quotient-equivalence-class-Algebra =
    map-equiv compute-quotient-Algebra

  equivalence-class-set-quotient-Algebra :
    type-quotient-Algebra →
    equivalence-class
      ( equivalence-relation-congruence-Algebra σ T A R)
  equivalence-class-set-quotient-Algebra =
    map-inv-equiv compute-quotient-Algebra

  is-inhabited-tuple-type-quotient-Algebra :
    {n : ℕ} →
    tuple type-quotient-Algebra n →
    type-trunc-Prop (tuple (type-Algebra σ T A) n)
  is-inhabited-tuple-type-quotient-Algebra empty-tuple =
    unit-trunc-Prop empty-tuple
  is-inhabited-tuple-type-quotient-Algebra (x ∷ v) =
    map-universal-property-trunc-Prop
      ( trunc-Prop _)
      ( λ (z , p) →
        map-trunc-Prop
          ( λ v' → z ∷ v')
          ( is-inhabited-tuple-type-quotient-Algebra v))
      ( pr2 (equivalence-class-set-quotient-Algebra x))

  relation-holds-for-all-tuples-sim-quotient-Algebra :
    {n : ℕ}
    (v v' : multivariable-input n ( λ _ → type-Algebra σ T A)) →
    sim-equivalence-relation
      ( all-sim-equivalence-relation n
        ( λ _ → type-Algebra σ T A)
        ( λ _ → equivalence-relation-congruence-Algebra σ T A R))
      ( v)
      ( v') →
    relation-holds-for-all-tuples-equivalence-relation-Algebra σ T A
      ( equivalence-relation-congruence-Algebra σ T A R)
      ( tuple-multivariable-input n (type-Algebra σ T A) v)
      ( tuple-multivariable-input n (type-Algebra σ T A) v')
  relation-holds-for-all-tuples-sim-quotient-Algebra
    {zero-ℕ} v v' p =
    raise-star
  relation-holds-for-all-tuples-sim-quotient-Algebra
    {succ-ℕ n} (x , v) (x' , v') (p , p') =
    ( p ,
      relation-holds-for-all-tuples-sim-quotient-Algebra
        ( v)
        ( v')
        ( p'))

  is-model-set-quotient-Algebra :
    is-model-of-signature σ set-quotient-Algebra
  is-model-set-quotient-Algebra op v =
    multivariable-map-set-quotient
      ( arity-operation-signature σ op)
      ( λ _ → type-Algebra σ T A)
      ( λ _ → equivalence-relation-congruence-Algebra σ T A R)
      ( equivalence-relation-congruence-Algebra σ T A R)
      ( pair
        ( λ v →
          is-model-set-Algebra σ T A op
            ( tuple-multivariable-input
              ( arity-operation-signature σ op)
              ( type-Algebra σ T A)
              ( v)))
        ( λ {v} {v'} p →
          preserves-operations-congruence-Algebra σ T A R op
            ( tuple-multivariable-input
              ( arity-operation-signature σ op)
              ( type-Algebra σ T A)
              ( v))
            ( tuple-multivariable-input
              ( arity-operation-signature σ op)
              ( type-Algebra σ T A)
              ( v'))
            ( relation-holds-for-all-tuples-sim-quotient-Algebra
              ( v)
              ( v')
              ( p))))
      ( multivariable-input-tuple
        ( arity-operation-signature σ op)
        ( type-quotient-Algebra)
        ( v))

  model-quotient-Algebra : Model-Of-Signature (l3 ⊔ l4) σ
  model-quotient-Algebra =
    ( set-quotient-Algebra , is-model-set-quotient-Algebra)
```

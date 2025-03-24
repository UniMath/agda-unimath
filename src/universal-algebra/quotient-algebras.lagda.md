# Quotient algebras

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module universal-algebra.quotient-algebras
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalence-classes funext univalence truncations
open import foundation.equivalence-relations funext univalence truncations
open import foundation.equivalences funext
open import foundation.functoriality-propositional-truncation funext univalence truncations
open import foundation.multivariable-functoriality-set-quotients funext univalence truncations
open import foundation.multivariable-operations funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.propositions funext univalence
open import foundation.raising-universe-levels-unit-type
open import foundation.set-quotients funext univalence truncations
open import foundation.sets funext univalence
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.vectors-set-quotients funext univalence truncations

open import linear-algebra.vectors funext univalence truncations

open import universal-algebra.algebraic-theories funext univalence truncations
open import universal-algebra.algebras-of-theories funext univalence truncations
open import universal-algebra.congruences funext univalence truncations
open import universal-algebra.models-of-signatures funext univalence truncations
open import universal-algebra.signatures funext univalence
```

</details>

## Idea

The quotient of an algebra by a congruence is the set quotient by that
congruence. This quotient again has the structure of an algebra inherited by the
original one.

## Definitions

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 : Level} ( Alg : Algebra Sg Th l3)
  { l4 : Level} ( R : congruence-Algebra Sg Th Alg l4)
  where

  set-quotient-Algebra : Set (l3 ⊔ l4)
  set-quotient-Algebra =
    quotient-Set ( equivalence-relation-congruence-Algebra Sg Th Alg R)

  type-quotient-Algebra : UU (l3 ⊔ l4)
  type-quotient-Algebra = pr1 set-quotient-Algebra

  is-set-set-quotient-Algebra : is-set type-quotient-Algebra
  is-set-set-quotient-Algebra = pr2 set-quotient-Algebra

  compute-quotient-Algebra :
    equivalence-class
      ( equivalence-relation-congruence-Algebra Sg Th Alg R) ≃
      ( type-quotient-Algebra)
  compute-quotient-Algebra =
    compute-set-quotient
      ( equivalence-relation-congruence-Algebra Sg Th Alg R)

  set-quotient-equivalence-class-Algebra :
    equivalence-class
      ( equivalence-relation-congruence-Algebra Sg Th Alg R) →
    type-quotient-Algebra
  set-quotient-equivalence-class-Algebra =
    map-equiv compute-quotient-Algebra

  equivalence-class-set-quotient-Algebra :
    type-quotient-Algebra →
    equivalence-class
      ( equivalence-relation-congruence-Algebra Sg Th Alg R)
  equivalence-class-set-quotient-Algebra =
    map-inv-equiv compute-quotient-Algebra

  vec-type-quotient-vec-type-Algebra :
    { n : ℕ} →
    vec type-quotient-Algebra n →
    type-trunc-Prop (vec (type-Algebra Sg Th Alg) n)
  vec-type-quotient-vec-type-Algebra empty-vec = unit-trunc-Prop empty-vec
  vec-type-quotient-vec-type-Algebra (x ∷ v) =
    map-universal-property-trunc-Prop
      ( trunc-Prop _)
      ( λ (z , p) →
        map-trunc-Prop
          (λ v' → z ∷ v')
          ( vec-type-quotient-vec-type-Algebra v))
      ( pr2 (equivalence-class-set-quotient-Algebra x))

  relation-holds-all-vec-all-sim-equivalence-relation :
    { n : ℕ}
    ( v v' : multivariable-input n ( λ _ → type-Algebra Sg Th Alg)) →
    ( type-Prop
      ( prop-equivalence-relation
        ( all-sim-equivalence-relation n
          ( λ _ → type-Algebra Sg Th Alg)
          ( λ _ → equivalence-relation-congruence-Algebra Sg Th Alg R)) v v')) →
    relation-holds-all-vec Sg Th Alg
      ( equivalence-relation-congruence-Algebra Sg Th Alg R)
      ( vector-multivariable-input n (type-Algebra Sg Th Alg) v)
      ( vector-multivariable-input n (type-Algebra Sg Th Alg) v')
  relation-holds-all-vec-all-sim-equivalence-relation {zero-ℕ} v v' p =
    raise-star
  relation-holds-all-vec-all-sim-equivalence-relation
    {succ-ℕ n} (x , v) (x' , v') (p , p') =
    p , (relation-holds-all-vec-all-sim-equivalence-relation v v' p')

  is-model-set-quotient-Algebra :
    is-model-signature Sg set-quotient-Algebra
  is-model-set-quotient-Algebra op v =
    multivariable-map-set-quotient
      ( arity-operation-signature Sg op)
      ( λ _ → type-Algebra Sg Th Alg)
      ( λ _ → equivalence-relation-congruence-Algebra Sg Th Alg R)
      ( equivalence-relation-congruence-Algebra Sg Th Alg R)
      ( pair
        ( λ v →
          is-model-set-Algebra Sg Th Alg op
            ( vector-multivariable-input
              ( arity-operation-signature Sg op)
              ( type-Algebra Sg Th Alg)
              ( v)))
        ( λ {v} {v'} p →
          preserves-operations-congruence-Algebra Sg Th Alg R op
            ( vector-multivariable-input
              ( arity-operation-signature Sg op)
              ( type-Algebra Sg Th Alg)
              ( v))
            ( vector-multivariable-input
              ( arity-operation-signature Sg op)
              ( type-Algebra Sg Th Alg)
              ( v'))
            (relation-holds-all-vec-all-sim-equivalence-relation v v' p)))
      ( multivariable-input-vector
        ( arity-operation-signature Sg op)
        ( type-quotient-Algebra)
        ( v))
```

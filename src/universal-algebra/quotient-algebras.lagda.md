# Quotient algebras

```agda
module universal-algebra.quotient-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.set-quotients
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.congruences
open import universal-algebra.signatures
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
  { l2 : Level } ( Th : Theory Sg l2)
  { l3 : Level } ( Alg : Algebra Sg Th l3)
  { l4 : Level } ( R : congruence-Algebra Sg Th Alg l4)
  where

  set-quotient-Algebra : Set (l3 ⊔ l4)
  set-quotient-Algebra =
    quotient-Set ( eq-rel-congruence-Algebra Sg Th Alg R)

  type-quotient-Algebra : UU (l3 ⊔ l4)
  type-quotient-Algebra = pr1 set-quotient-Algebra

  is-set-set-quotient-Algebra : is-set type-quotient-Algebra
  is-set-set-quotient-Algebra = pr2 set-quotient-Algebra

  compute-quotient-Algebra :
    equivalence-class
      ( eq-rel-congruence-Algebra Sg Th Alg R) ≃
      ( type-quotient-Algebra)
  compute-quotient-Algebra =
    compute-set-quotient
      ( eq-rel-congruence-Algebra Sg Th Alg R)

  set-quotient-equivalence-class-Algebra :
    equivalence-class
      ( eq-rel-congruence-Algebra Sg Th Alg R) →
    type-quotient-Algebra
  set-quotient-equivalence-class-Algebra =
    map-equiv compute-quotient-Algebra

  equivalence-class-set-quotient-Algebra :
    type-quotient-Algebra →
    equivalence-class
      ( eq-rel-congruence-Algebra Sg Th Alg R)
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
```

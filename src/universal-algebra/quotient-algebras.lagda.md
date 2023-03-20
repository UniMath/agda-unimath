# Quotient Algebras

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
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.set-quotients
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-theories
open import universal-algebra.models-signatures
open import universal-algebra.signatures
```

</details>

## Idea

The quotient of an algebra by a congruence is the set quotient by that
congruence. The operations are inherited by the original algebra.

## Definitions

```agda
module _
  { l1 : Level} ( Sig : signature l1)
  { l2 : Level } ( Th : Theory Sig l2)
  { l3 : Level } ( Alg : Algebra Sig Th l3)
  { l4 : Level } ( R : Eq-Rel l4 (type-Algebra Sig Th Alg))
  where

  set-quotient-Algebra : Set (l3 ⊔ l4)
  set-quotient-Algebra = quotient-Set R

  type-quotient-Algebra : UU (l3 ⊔ l4)
  type-quotient-Algebra = pr1 set-quotient-Algebra

  is-set-set-quotient-Algebra : is-set type-quotient-Algebra
  is-set-set-quotient-Algebra = pr2 set-quotient-Algebra

  compute-quotient-Algebra :
    equivalence-class R ≃ type-quotient-Algebra
  compute-quotient-Algebra = compute-set-quotient R

  set-quotient-equivalence-class-Algebra :
    equivalence-class R → type-quotient-Algebra
  set-quotient-equivalence-class-Algebra =
    map-equiv compute-quotient-Algebra

  equivalence-class-set-quotient-Algebra :
    type-quotient-Algebra → equivalence-class R
  equivalence-class-set-quotient-Algebra =
    map-inv-equiv compute-quotient-Algebra

  vec-type-quotient-vec-type-Algebra :
    { n : ℕ} →
    vec type-quotient-Algebra n →
    type-trunc-Prop (vec (type-Algebra Sig Th Alg) n)
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

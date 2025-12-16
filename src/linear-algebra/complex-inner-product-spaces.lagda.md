# Complex inner product spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.complex-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.multiplication-complex-numbers
open import complex-numbers.real-complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.complex-vector-spaces
open import linear-algebra.sesquilinear-forms-complex-vector-spaces

open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Vector-Space l1 l2)
  (f : sesquilinear-form-ℂ-Vector-Space V)
  where

  is-conjugate-symmetric-prop-sesquilinear-form-ℂ-Vector-Space :
    Prop (lsuc l1 ⊔ l2)
  is-conjugate-symmetric-prop-sesquilinear-form-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℂ-Vector-Space V)
          ( λ y →
            Id-Prop
              ( ℂ-Set l1)
              ( map-sesquilinear-form-ℂ-Vector-Space V f x y)
              ( conjugate-ℂ (map-sesquilinear-form-ℂ-Vector-Space V f y x))))

  is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-conjugate-symmetric-prop-sesquilinear-form-ℂ-Vector-Space

  is-semidefinite-prop-sesquilinear-form-ℂ-Vector-Space : Prop (l1 ⊔ l2)
  is-semidefinite-prop-sesquilinear-form-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        is-nonnegative-prop-ℝ
          ( re-ℂ (map-sesquilinear-form-ℂ-Vector-Space V f x x)))

  is-semidefinite-sesquilinear-form-ℂ-Vector-Space : UU (l1 ⊔ l2)
  is-semidefinite-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-semidefinite-prop-sesquilinear-form-ℂ-Vector-Space

  is-extensional-prop-sesquilinear-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-extensional-prop-sesquilinear-form-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        ( Id-Prop
          ( ℂ-Set l1)
          ( map-sesquilinear-form-ℂ-Vector-Space V f x x)
          ( raise-ℂ l1 zero-ℂ)) ⇒
        ( Id-Prop
          ( set-ℂ-Vector-Space V)
          ( x)
          ( zero-ℂ-Vector-Space V)))

  is-extensional-sesquilinear-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-extensional-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-extensional-prop-sesquilinear-form-ℂ-Vector-Space

  is-inner-product-prop-sesquilinear-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-inner-product-prop-sesquilinear-form-ℂ-Vector-Space =
    ( is-conjugate-symmetric-prop-sesquilinear-form-ℂ-Vector-Space) ∧
    ( is-semidefinite-prop-sesquilinear-form-ℂ-Vector-Space) ∧
    ( is-extensional-prop-sesquilinear-form-ℂ-Vector-Space)

  is-inner-product-sesquilinear-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-inner-product-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-inner-product-prop-sesquilinear-form-ℂ-Vector-Space

ℂ-Inner-Product-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℂ-Inner-Product-Space l1 l2 =
  Σ
    ( ℂ-Vector-Space l1 l2)
    ( λ V →
      Σ ( sesquilinear-form-ℂ-Vector-Space V)
        ( is-inner-product-sesquilinear-form-ℂ-Vector-Space V))

module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  vector-space-ℂ-Inner-Product-Space : ℂ-Vector-Space l1 l2
  vector-space-ℂ-Inner-Product-Space = pr1 V

  sesquilinear-form-inner-product-ℂ-Inner-Product-Space :
    sesquilinear-form-ℂ-Vector-Space vector-space-ℂ-Inner-Product-Space
  sesquilinear-form-inner-product-ℂ-Inner-Product-Space = pr1 (pr2 V)

  type-ℂ-Inner-Product-Space : UU l2
  type-ℂ-Inner-Product-Space =
    type-ℂ-Vector-Space vector-space-ℂ-Inner-Product-Space

  inner-product-ℂ-Inner-Product-Space :
    type-ℂ-Inner-Product-Space → type-ℂ-Inner-Product-Space → ℂ l1
  inner-product-ℂ-Inner-Product-Space =
    map-sesquilinear-form-ℂ-Vector-Space
      ( vector-space-ℂ-Inner-Product-Space)
      ( sesquilinear-form-inner-product-ℂ-Inner-Product-Space)

  is-conjugate-symmetric-inner-product-ℂ-Inner-Product-Space :
    (x y : type-ℂ-Inner-Product-Space) →
    inner-product-ℂ-Inner-Product-Space x y ＝
    conjugate-ℂ (inner-product-ℂ-Inner-Product-Space y x)
  is-conjugate-symmetric-inner-product-ℂ-Inner-Product-Space = pr1 (pr2 (pr2 V))

  abstract
    is-real-diagonal-inner-product-ℂ-Inner-Product-Space :
      (x : type-ℂ-Inner-Product-Space) →
      is-real-ℂ (inner-product-ℂ-Inner-Product-Space x x)
```

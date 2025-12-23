# Complex inner product spaces are normed

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.complex-inner-product-spaces-are-normed where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.magnitude-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.cauchy-schwarz-inequality-complex-inner-product-spaces
open import linear-algebra.complex-inner-product-spaces
open import linear-algebra.normed-complex-vector-spaces
open import linear-algebra.seminormed-complex-vector-spaces

open import metric-spaces.metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

For any
[complex inner product space](linear-algebra.complex-inner-product-spaces.md)
`V`, the function $v ↦ \sqrt{v · v}$ satisfies the properties of a
[norm](linear-algebra.normed-complex-vector-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    is-triangular-squared-norm-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      leq-ℝ
        ( squared-norm-ℂ-Inner-Product-Space V
          ( add-ℂ-Inner-Product-Space V u v))
        ( square-ℝ
          ( ( map-norm-ℂ-Inner-Product-Space V u) +ℝ
            ( map-norm-ℂ-Inner-Product-Space V v)))
    is-triangular-squared-norm-ℂ-Inner-Product-Space u v =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
        squared-norm-ℂ-Inner-Product-Space V (add-ℂ-Inner-Product-Space V u v)
        ≤ ( squared-norm-ℂ-Inner-Product-Space V u) +ℝ
          ( real-ℕ 2 *ℝ re-ℂ (inner-product-ℂ-Inner-Product-Space V u v)) +ℝ
          ( squared-norm-ℂ-Inner-Product-Space V v)
          by leq-eq-ℝ (squared-norm-add-ℂ-Inner-Product-Space V u v)
        ≤ ( square-ℝ (map-norm-ℂ-Inner-Product-Space V u)) +ℝ
          ( ( real-ℕ 2) *ℝ
            ( magnitude-ℂ (inner-product-ℂ-Inner-Product-Space V u v))) +ℝ
          ( square-ℝ (map-norm-ℂ-Inner-Product-Space V v))
          by
            preserves-leq-add-ℝ
              ( preserves-leq-add-ℝ
                ( leq-eq-ℝ
                  ( inv
                    ( eq-real-square-sqrt-ℝ⁰⁺
                      ( nonnegative-squared-norm-ℂ-Inner-Product-Space V u))))
                ( preserves-leq-left-mul-ℝ⁰⁺
                  ( nonnegative-real-ℕ 2)
                  ( leq-re-magnitude-ℂ _)))
              ( leq-eq-ℝ
                ( inv
                  ( eq-real-square-sqrt-ℝ⁰⁺
                    ( nonnegative-squared-norm-ℂ-Inner-Product-Space V v))))
        ≤ ( square-ℝ (map-norm-ℂ-Inner-Product-Space V u)) +ℝ
          ( ( real-ℕ 2) *ℝ
            ( ( map-norm-ℂ-Inner-Product-Space V u) *ℝ
              ( map-norm-ℂ-Inner-Product-Space V v))) +ℝ
          ( square-ℝ (map-norm-ℂ-Inner-Product-Space V v))
          by
            preserves-leq-right-add-ℝ _ _ _
              ( preserves-leq-left-add-ℝ _ _ _
                ( preserves-leq-left-mul-ℝ⁰⁺
                  ( nonnegative-real-ℕ 2)
                  ( cauchy-schwarz-inequality-ℂ-Inner-Product-Space V u v)))
        ≤ square-ℝ
            ( ( map-norm-ℂ-Inner-Product-Space V u) +ℝ
              ( map-norm-ℂ-Inner-Product-Space V v))
        by leq-eq-ℝ (inv (square-add-ℝ _ _))

    is-triangular-norm-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      leq-ℝ
        ( map-norm-ℂ-Inner-Product-Space V (add-ℂ-Inner-Product-Space V u v))
        ( ( map-norm-ℂ-Inner-Product-Space V u) +ℝ
          ( map-norm-ℂ-Inner-Product-Space V v))
    is-triangular-norm-ℂ-Inner-Product-Space u v =
      tr
        ( leq-ℝ _)
        ( ( inv (eq-abs-sqrt-square-ℝ _)) ∙
          ( abs-real-ℝ⁰⁺
            ( ( nonnegative-norm-ℂ-Inner-Product-Space V u) +ℝ⁰⁺
              ( nonnegative-norm-ℂ-Inner-Product-Space V v))))
        ( preserves-leq-sqrt-ℝ⁰⁺
          ( nonnegative-squared-norm-ℂ-Inner-Product-Space V
            ( add-ℂ-Inner-Product-Space V u v))
          ( nonnegative-square-ℝ
            ( ( map-norm-ℂ-Inner-Product-Space V u) +ℝ
              ( map-norm-ℂ-Inner-Product-Space V v)))
          ( is-triangular-squared-norm-ℂ-Inner-Product-Space u v))

  is-seminorm-norm-ℂ-Inner-Product-Space :
    is-seminorm-ℂ-Vector-Space
      ( vector-space-ℂ-Inner-Product-Space V)
      ( map-norm-ℂ-Inner-Product-Space V)
  is-seminorm-norm-ℂ-Inner-Product-Space =
    ( is-triangular-norm-ℂ-Inner-Product-Space ,
      norm-mul-ℂ-Inner-Product-Space V)

  seminorm-ℂ-Inner-Product-Space :
    seminorm-ℂ-Vector-Space (vector-space-ℂ-Inner-Product-Space V)
  seminorm-ℂ-Inner-Product-Space =
    ( map-norm-ℂ-Inner-Product-Space V , is-seminorm-norm-ℂ-Inner-Product-Space)

  is-norm-seminorm-ℂ-Inner-Product-Space :
    is-norm-seminorm-ℂ-Vector-Space
      ( vector-space-ℂ-Inner-Product-Space V)
      ( seminorm-ℂ-Inner-Product-Space)
  is-norm-seminorm-ℂ-Inner-Product-Space =
    is-extensional-norm-ℂ-Inner-Product-Space V

  norm-ℂ-Inner-Product-Space :
    norm-ℂ-Vector-Space (vector-space-ℂ-Inner-Product-Space V)
  norm-ℂ-Inner-Product-Space =
    ( seminorm-ℂ-Inner-Product-Space , is-norm-seminorm-ℂ-Inner-Product-Space)

  normed-vector-space-ℂ-Inner-Product-Space : Normed-ℂ-Vector-Space l1 l2
  normed-vector-space-ℂ-Inner-Product-Space =
    ( vector-space-ℂ-Inner-Product-Space V ,
      norm-ℂ-Inner-Product-Space)

  metric-space-ℂ-Inner-Product-Space : Metric-Space l2 l1
  metric-space-ℂ-Inner-Product-Space =
    metric-space-Normed-ℂ-Vector-Space
      ( normed-vector-space-ℂ-Inner-Product-Space)
```

# Real inner product spaces are normed

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.real-inner-product-spaces-are-normed where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.cauchy-schwarz-inequality-real-inner-product-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-inner-product-spaces
open import linear-algebra.seminormed-real-vector-spaces

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

Given a [real inner product space](linear-algebra.real-inner-product-spaces.md)
`V`, defining the norm of `v` as the
[square root](real-numbers.square-roots-nonnegative-real-numbers.md) of the
inner product of `v` with itself satisfies the conditions of a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    is-triangular-squared-norm-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) →
      leq-ℝ
        ( squared-norm-ℝ-Inner-Product-Space V
          ( add-ℝ-Inner-Product-Space V u v))
        ( square-ℝ
          ( ( norm-ℝ-Inner-Product-Space V u) +ℝ
            ( norm-ℝ-Inner-Product-Space V v)))
    is-triangular-squared-norm-ℝ-Inner-Product-Space u v =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          squared-norm-ℝ-Inner-Product-Space V (add-ℝ-Inner-Product-Space V u v)
          ≤ ( squared-norm-ℝ-Inner-Product-Space V u) +ℝ
            ( real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V u v) +ℝ
            ( squared-norm-ℝ-Inner-Product-Space V v)
            by leq-eq-ℝ (squared-norm-add-ℝ-Inner-Product-Space V u v)
          ≤ ( squared-norm-ℝ-Inner-Product-Space V u) +ℝ
            ( ( real-ℕ 2) *ℝ
              ( ( norm-ℝ-Inner-Product-Space V u) *ℝ
                  norm-ℝ-Inner-Product-Space V v)) +ℝ
            ( squared-norm-ℝ-Inner-Product-Space V v)
            by
              preserves-leq-right-add-ℝ _ _ _
                ( preserves-leq-left-add-ℝ _ _ _
                  ( preserves-leq-left-mul-ℝ⁺
                    ( positive-real-ℕ⁺ (2 , λ ()))
                    ( transitive-leq-ℝ _ _ _
                      ( cauchy-schwarz-inequality-ℝ-Inner-Product-Space V u v)
                      ( leq-abs-ℝ _))))
          ≤ ( square-ℝ (norm-ℝ-Inner-Product-Space V u)) +ℝ
            ( ( real-ℕ 2) *ℝ
              ( ( norm-ℝ-Inner-Product-Space V u) *ℝ
                  norm-ℝ-Inner-Product-Space V v)) +ℝ
            ( square-ℝ (norm-ℝ-Inner-Product-Space V v))
            by
              leq-eq-ℝ
                ( ap-add-ℝ
                  ( ap-add-ℝ
                    ( inv
                      ( eq-real-square-sqrt-ℝ⁰⁺
                        ( nonnegative-squared-norm-ℝ-Inner-Product-Space V u)))
                    ( refl))
                  ( inv
                    ( eq-real-square-sqrt-ℝ⁰⁺
                      ( nonnegative-squared-norm-ℝ-Inner-Product-Space V v))))
          ≤ square-ℝ
              ( ( norm-ℝ-Inner-Product-Space V u) +ℝ
                ( norm-ℝ-Inner-Product-Space V v))
            by leq-eq-ℝ (inv (square-add-ℝ _ _))

    is-triangular-norm-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) →
      leq-ℝ
        ( norm-ℝ-Inner-Product-Space V (add-ℝ-Inner-Product-Space V u v))
        ( norm-ℝ-Inner-Product-Space V u +ℝ norm-ℝ-Inner-Product-Space V v)
    is-triangular-norm-ℝ-Inner-Product-Space u v =
      tr
        ( leq-ℝ _)
        ( ( inv (eq-abs-sqrt-square-ℝ _)) ∙
          ( abs-real-ℝ⁰⁺
            ( ( nonnegative-norm-ℝ-Inner-Product-Space V u) +ℝ⁰⁺
              ( nonnegative-norm-ℝ-Inner-Product-Space V v))))
        ( preserves-leq-sqrt-ℝ⁰⁺
          ( nonnegative-squared-norm-ℝ-Inner-Product-Space V
            ( add-ℝ-Inner-Product-Space V u v))
          ( nonnegative-square-ℝ
            ( norm-ℝ-Inner-Product-Space V u +ℝ norm-ℝ-Inner-Product-Space V v))
          ( is-triangular-squared-norm-ℝ-Inner-Product-Space u v))

  is-seminorm-norm-ℝ-Inner-Product-Space :
    is-seminorm-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space V)
      ( norm-ℝ-Inner-Product-Space V)
  is-seminorm-norm-ℝ-Inner-Product-Space =
    ( is-triangular-norm-ℝ-Inner-Product-Space ,
      is-absolutely-homogeneous-norm-ℝ-Inner-Product-Space V)

  abstract
    is-extensional-norm-ℝ-Inner-Product-Space :
      (v : type-ℝ-Inner-Product-Space V) →
      (norm-ℝ-Inner-Product-Space V v ＝ raise-ℝ l1 zero-ℝ) →
      is-zero-ℝ-Inner-Product-Space V v
    is-extensional-norm-ℝ-Inner-Product-Space v ∥v∥=0 =
      is-extensional-diagonal-inner-product-ℝ-Inner-Product-Space
        ( V)
        ( v)
        ( equational-reasoning
          squared-norm-ℝ-Inner-Product-Space V v
          ＝ square-ℝ (norm-ℝ-Inner-Product-Space V v)
            by
              inv
                ( eq-real-square-sqrt-ℝ⁰⁺
                  ( nonnegative-squared-norm-ℝ-Inner-Product-Space V v))
          ＝ square-ℝ (raise-ℝ l1 zero-ℝ)
            by ap square-ℝ ∥v∥=0
          ＝ raise-ℝ l1 (square-ℝ zero-ℝ)
            by square-raise-ℝ l1 _
          ＝ raise-ℝ l1 zero-ℝ
            by ap (raise-ℝ l1) square-zero-ℝ)

  norm-normed-vector-space-ℝ-Inner-Product-Space :
    norm-ℝ-Vector-Space (vector-space-ℝ-Inner-Product-Space V)
  norm-normed-vector-space-ℝ-Inner-Product-Space =
    ( ( norm-ℝ-Inner-Product-Space V ,
        is-seminorm-norm-ℝ-Inner-Product-Space) ,
      is-extensional-norm-ℝ-Inner-Product-Space)

  normed-vector-space-ℝ-Inner-Product-Space : Normed-ℝ-Vector-Space l1 l2
  normed-vector-space-ℝ-Inner-Product-Space =
    ( vector-space-ℝ-Inner-Product-Space V ,
      norm-normed-vector-space-ℝ-Inner-Product-Space)

  metric-space-ℝ-Inner-Product-Space : Metric-Space l2 l1
  metric-space-ℝ-Inner-Product-Space =
    metric-space-Normed-ℝ-Vector-Space normed-vector-space-ℝ-Inner-Product-Space
```

## Properties

### The metric space of the inner product space of `ℝ` over itself is the standard metric space of `ℝ`

```agda
abstract
  eq-metric-space-real-inner-product-space-ℝ :
    (l : Level) →
    metric-space-ℝ-Inner-Product-Space (real-inner-product-space-ℝ l) ＝
    metric-space-ℝ l
  eq-metric-space-real-inner-product-space-ℝ l =
    ( eq-isometric-eq-Metric-Space _ _
      ( refl ,
        λ d x y →
          iff-eq
            ( ap
              ( λ m → leq-prop-ℝ m (real-ℚ⁺ d))
              ( inv (eq-abs-sqrt-square-ℝ _))))) ∙
    ( eq-metric-space-normed-real-vector-space-metric-space-ℝ l)
```

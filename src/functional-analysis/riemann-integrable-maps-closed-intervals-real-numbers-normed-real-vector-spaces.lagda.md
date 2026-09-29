# Riemann integrable maps from closed intervals of real numbers to normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.riemann-integrable-maps-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.riemann-sums-tagged-partitions-closed-intervals-real-numbers-normed-real-vector-spaces

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.limits-of-sequences-metric-spaces

open import order-theory.large-posets

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.partitions-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.standard-uniform-partitions-closed-intervals-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.tagged-partitions-closed-intervals-real-numbers
open import real-numbers.unit-fractions-real-numbers
```

</details>

## Idea

Given a [closed interval](real-numbers.closed-intervals-real-numbers.md)
`[a, b]` in the [real numbers](real-numbers.dedekind-real-numbers.md) and a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`, a
{{#concept "Riemann integral" WDID=Q697181 WD="Riemann integral" Disambiguation="of a map from a closed interval in ℝ to a normed real vector space" Agda=is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space}}
of `f` over `[a, b]` is `x` if there
[exists](foundation.existential-quantification.md) a modulus function
`μ : ℚ⁺ → ℚ⁺` such that for every
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
and any
[tagged partition](real-numbers.tagged-partitions-closed-intervals-real-numbers.md)
`p` of `[a, b]` with mesh at most `μ ε`, the
[Riemann sum](functional-analysis.riemann-sums-tagged-partitions-closed-intervals-real-numbers-normed-real-vector-spaces.md)
of `f` over `p` is within an `ε`-neighborhood of `x`. If such an `x` exists, `f`
is said to be
{{#concept "Riemann integrable" Disambiguation="a map from a closed interval in ℝ to a normed real vector space" Agda=is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space}}
over `[a, b]`, and that `x` is unique.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  where

  is-riemann-integral-modulus-prop-map-closed-interval-real-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → subtype (lsuc l1) (ℚ⁺ → ℚ⁺)
  is-riemann-integral-modulus-prop-map-closed-interval-real-Normed-ℝ-Vector-Space
    x μ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( tagged-partition-closed-interval-ℝ [a,b])
          ( λ tp →
            hom-Prop
              ( leq-prop-ℝ⁰⁺
                ( mesh-tagged-partition-closed-interval-ℝ [a,b] tp)
                ( nonnegative-real-ℚ⁺ (μ ε)))
              ( neighborhood-prop-Normed-ℝ-Vector-Space
                ( V)
                ( ε)
                ( riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space
                  ( V)
                  ( [a,b])
                  ( f)
                  ( tp))
                ( x))))

  is-riemann-integral-prop-map-closed-interval-real-Normed-ℝ-Vector-Space :
    subtype (lsuc l1) (type-Normed-ℝ-Vector-Space V)
  is-riemann-integral-prop-map-closed-interval-real-Normed-ℝ-Vector-Space x =
    ∃ ( ℚ⁺ → ℚ⁺)
      ( is-riemann-integral-modulus-prop-map-closed-interval-real-Normed-ℝ-Vector-Space
        ( x))

  is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → UU (lsuc l1)
  is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space =
    is-in-subtype
      ( is-riemann-integral-prop-map-closed-interval-real-Normed-ℝ-Vector-Space)

  is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space :
    UU (lsuc l1 ⊔ l2)
  is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space =
    Σ ( type-Normed-ℝ-Vector-Space V)
      ( is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space)

riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} →
  Normed-ℝ-Vector-Space l1 l2 → closed-interval-ℝ l1 l1 → UU (lsuc l1 ⊔ l2)
riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space {l1} V [a,b] =
  Σ ( type-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
    ( is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b]))
```

## Properties

### If a function is Riemann integrable, the integral is the limit as `n → ∞` of the Riemann sum on the standard uniform partition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  ((S , is-integral-S) :
    is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f))
  where abstract

  is-limit-riemann-sum-tag-lower-bound-standard-uniform-partition-is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space :
    is-limit-sequence-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( riemann-sum-tag-lower-bound-standard-uniform-partition-closed-interval-ℝ
        ( V)
        ( [a,b])
        ( f))
      ( S)
  is-limit-riemann-sum-tag-lower-bound-standard-uniform-partition-is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space =
    let
      open
        do-syntax-trunc-Prop
          ( is-limit-prop-sequence-Metric-Space
            ( metric-space-Normed-ℝ-Vector-Space V)
            ( riemann-sum-tag-lower-bound-standard-uniform-partition-closed-interval-ℝ
              ( V)
              ( [a,b])
              ( f))
            ( S))
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in do
      (μ , is-mod-μ) ← is-integral-S
      (q , b-a<q) ←
        exists-greater-positive-rational-ℝ (width-closed-interval-ℝ [a,b])
      intro-exists
        ( λ ε → pred-nonzero-ℕ (pr1 (smaller-reciprocal-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ μ ε))))
        ( λ ε n N≤n →
          let (N , 1/N≤με/q) = smaller-reciprocal-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ μ ε) in
          is-mod-μ
            ( ε)
            ( tag-lower-bounds-partition-closed-interval-ℝ
              ( [a,b])
              ( partition-standard-uniform-partition-closed-interval-ℝ
                ( [a,b])
                ( n)))
            ( chain-of-inequalities
              real-ℝ⁰⁺
                ( mesh-partition-closed-interval-ℝ
                  ( [a,b])
                  ( partition-standard-uniform-partition-closed-interval-ℝ
                    ( [a,b])
                    ( n)))
              ≤ width-closed-interval-ℝ [a,b] *ℝ reciprocal-real-succ-ℕ n
                by
                  leq-eq-ℝ
                    ( ap
                      ( real-ℝ⁰⁺)
                      ( compute-mesh-standard-uniform-partition-closed-interval-ℝ
                        ( [a,b])
                        ( n)))
              ≤ real-ℚ⁺ q *ℝ reciprocal-real-ℕ⁺ N
                by
                  preserves-leq-mul-ℝ⁰⁺
                    ( nonnegative-width-closed-interval-ℝ [a,b])
                    ( nonnegative-real-ℚ⁺ q)
                    ( nonnegative-reciprocal-real-succ-ℕ n)
                    ( nonnegative-reciprocal-real-ℕ⁺ N)
                    ( leq-le-ℝ b-a<q)
                    ( preserves-leq-real-ℚ
                      ( leq-reciprocal-rational-ℕ⁺
                        ( N)
                        ( succ-nonzero-ℕ' n)
                        ( concatenate-eq-leq-ℕ
                          ( succ-ℕ n)
                          ( ap
                            ( nat-ℕ⁺)
                            ( inv (is-section-succ-nonzero-ℕ' _)))
                          ( N≤n))))
              ≤ real-ℚ⁺ q *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ μ ε)
                by
                  preserves-leq-left-mul-ℝ⁰⁺
                    ( nonnegative-real-ℚ⁺ q)
                    ( preserves-leq-real-ℚ (leq-le-ℚ⁺ 1/N≤με/q))
              ≤ real-ℚ⁺ (q *ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ μ ε))
                by leq-eq-ℝ (mul-real-ℚ _ _)
              ≤ real-ℚ⁺ (μ ε)
                by leq-eq-ℝ (ap real-ℚ (is-section-left-div-ℚ⁺ q _))))

module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  where

  abstract
    all-elements-equal-is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space :
      all-elements-equal
        ( is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f))
    all-elements-equal-is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space
      (S , is-integral-S) (T , is-integral-T) =
      eq-type-subtype
        ( is-riemann-integral-prop-map-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f))
        ( eq-limit-sequence-Metric-Space
          ( metric-space-Normed-ℝ-Vector-Space V)
          ( riemann-sum-tag-lower-bound-standard-uniform-partition-closed-interval-ℝ
            ( V)
            ( [a,b])
            ( f))
          ( S)
          ( T)
          ( is-limit-riemann-sum-tag-lower-bound-standard-uniform-partition-is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f)
            ( S , is-integral-S))
          ( is-limit-riemann-sum-tag-lower-bound-standard-uniform-partition-is-riemann-integral-map-closed-interval-real-Normed-ℝ-Vector-Space
            ( V)
            ( [a,b])
            ( f)
            ( T , is-integral-T)))

    is-prop-is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space :
      is-prop
        ( is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space
          ( V)
          ( [a,b])
          ( f))
    is-prop-is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space =
      is-prop-all-elements-equal
        ( all-elements-equal-is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space)

  is-riemann-integrable-prop-map-closed-interval-real-Normed-ℝ-Vector-Space :
    Prop (lsuc l1 ⊔ l2)
  is-riemann-integrable-prop-map-closed-interval-real-Normed-ℝ-Vector-Space =
    ( is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( f) ,
      is-prop-is-riemann-integrable-map-closed-interval-real-Normed-ℝ-Vector-Space)
```

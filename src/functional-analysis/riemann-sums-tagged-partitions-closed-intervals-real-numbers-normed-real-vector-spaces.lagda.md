# Riemann sums over tagged partitions of a closed interval in the real numbers of functions from that interval to real vector spaces

```agda
module functional-analysis.riemann-sums-tagged-partitions-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-normed-real-vector-spaces

open import lists.finite-sequences

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.partitions-closed-intervals-real-numbers
open import real-numbers.standard-uniform-partitions-closed-intervals-real-numbers
open import real-numbers.tagged-partitions-closed-intervals-real-numbers
```

</details>

## Idea

Given a [closed interval](real-numbers.closed-intervals-real-numbers.md)
`[a, b]` in the [real numbers](real-numbers.dedekind-real-numbers.md), a
[tagged partition](real-numbers.tagged-partitions-closed-intervals-real-numbers.md)
`p` of `[a, b]`, a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`, and
a function `f : [a, b] → V`, the
{{#concept "Riemann sum" Disambiguation="of a function from a closed interval into a normed real vector space, on a tagged partition of the interval"}}
of `f` on `p` is the sum over the tagged partitions in `p` (with tag `tᵢ` for
interval `[aᵢ, bᵢ]`) of `(bᵢ - aᵢ) * f tᵢ`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  (tp@(p , t) : tagged-partition-closed-interval-ℝ [a,b])
  (let n = pred-length-partition-closed-interval-ℝ [a,b] p)
  where

  fin-sequence-values-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space :
    fin-sequence (type-Normed-ℝ-Vector-Space V) n
  fin-sequence-values-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space =
    f ∘ fin-sequence-tags-elements-tagged-partition-closed-interval-ℝ [a,b] tp

  fin-sequence-weights-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space :
    fin-sequence (ℝ l1) n
  fin-sequence-weights-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space =
    width-closed-interval-ℝ ∘
    fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p

  riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V
  riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space =
    sum-fin-sequence-type-Normed-ℝ-Vector-Space
      ( V)
      ( n)
      ( λ i →
        mul-Normed-ℝ-Vector-Space V
          ( fin-sequence-weights-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space
            ( i))
          ( fin-sequence-values-riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space
            ( i)))
```

## Properties

### Riemann sums over the standard uniform partition of an interval, with partitions tagged with their lower bounds

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : closed-interval-ℝ l1 l1)
  (f : type-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V)
  (n : ℕ)
  where

  riemann-sum-tag-lower-bound-standard-uniform-partition-closed-interval-ℝ :
    type-Normed-ℝ-Vector-Space V
  riemann-sum-tag-lower-bound-standard-uniform-partition-closed-interval-ℝ =
    riemann-sum-tagged-partition-map-closed-interval-real-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( f)
      ( tag-lower-bounds-partition-closed-interval-ℝ
        ( [a,b])
        ( partition-standard-uniform-partition-closed-interval-ℝ [a,b] n))
```

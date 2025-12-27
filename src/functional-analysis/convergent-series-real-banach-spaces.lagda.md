# Convergent series in real Banach spaces

```agda
module functional-analysis.convergent-series-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-complete-metric-abelian-groups
open import analysis.convergent-series-metric-abelian-groups
open import analysis.convergent-series-real-numbers
open import analysis.series-real-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.additive-complete-metric-abelian-groups-real-banach-spaces
open import functional-analysis.real-banach-spaces
open import functional-analysis.series-real-banach-spaces

open import linear-algebra.normed-real-vector-spaces

open import lists.sequences

open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [series](functional-analysis.series-real-banach-spaces.md)
[converges](analysis.convergent-series-metric-abelian-groups.md) in a
[real Banach space](functional-analysis.real-banach-spaces.md) if its partial
sums form a [Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md).

A slightly modified converse is also true: if a series converges, there
[exists](foundation.existential-quantification.md) a modulus making its partial
sums a Cauchy sequence.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  is-sum-prop-series-ℝ-Banach-Space : type-ℝ-Banach-Space V → Prop l1
  is-sum-prop-series-ℝ-Banach-Space = is-sum-prop-series-Metric-Ab σ

  is-sum-series-ℝ-Banach-Space : type-ℝ-Banach-Space V → UU l1
  is-sum-series-ℝ-Banach-Space = is-sum-series-Metric-Ab σ

  is-convergent-prop-series-ℝ-Banach-Space : Prop (l1 ⊔ l2)
  is-convergent-prop-series-ℝ-Banach-Space =
    is-convergent-prop-series-Metric-Ab σ

  is-convergent-series-ℝ-Banach-Space : UU (l1 ⊔ l2)
  is-convergent-series-ℝ-Banach-Space = is-convergent-series-Metric-Ab σ

convergent-series-ℝ-Banach-Space :
  {l1 l2 : Level} (V : ℝ-Banach-Space l1 l2) → UU (l1 ⊔ l2)
convergent-series-ℝ-Banach-Space V =
  type-subtype (is-convergent-prop-series-ℝ-Banach-Space V)
```

## Properties

### If the partial sums of a series form a Cauchy sequence, the series converges

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  is-convergent-is-cauchy-sequence-partial-sum-series-ℝ-Banach-Space :
    is-cauchy-sequence-Metric-Space
      ( metric-space-ℝ-Banach-Space V)
      ( partial-sum-series-ℝ-Banach-Space V σ) →
    is-convergent-series-ℝ-Banach-Space V σ
  is-convergent-is-cauchy-sequence-partial-sum-series-ℝ-Banach-Space =
    is-convergent-is-cauchy-sequence-partial-sum-series-Complete-Metric-Ab
      ( complete-metric-ab-add-ℝ-Banach-Space V)
      ( σ)
```

### A series in the real Banach space of real numbers converges if and only if its corresponding series of real numbers converges

```agda
module _
  {l : Level}
  (σ : sequence (ℝ l))
  where

  is-convergent-real-is-convergent-real-banach-space-ℝ :
    is-convergent-series-ℝ-Banach-Space
      ( real-banach-space-ℝ l)
      ( series-terms-ℝ-Banach-Space (real-banach-space-ℝ l) σ) →
    is-convergent-series-ℝ (series-terms-ℝ σ)
  is-convergent-real-is-convergent-real-banach-space-ℝ (lim , is-lim) =
    ( lim ,
      preserves-limits-sequences-isometry-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space (normed-real-vector-space-ℝ l))
        ( metric-space-ℝ l)
        ( id , λ d x y → inv-iff (neighborhood-iff-leq-dist-ℝ d x y))
        ( λ n → sum-fin-sequence-ℝ n (σ ∘ nat-Fin n))
        ( lim)
        ( is-lim))

  is-convergent-real-banach-space-is-convergent-ℝ :
    is-convergent-series-ℝ (series-terms-ℝ σ) →
    is-convergent-series-ℝ-Banach-Space
      ( real-banach-space-ℝ l)
      ( series-terms-ℝ-Banach-Space (real-banach-space-ℝ l) σ)
  is-convergent-real-banach-space-is-convergent-ℝ (lim , is-lim) =
    ( lim ,
      preserves-limits-sequences-isometry-Metric-Space
        ( metric-space-ℝ l)
        ( metric-space-Normed-ℝ-Vector-Space (normed-real-vector-space-ℝ l))
        ( id , λ d x y → neighborhood-iff-leq-dist-ℝ d x y)
        ( λ n → sum-fin-sequence-ℝ n (σ ∘ nat-Fin n))
        ( lim)
        ( is-lim))
```

### If a series converges, there exists a modulus making its partial sums a Cauchy sequence

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  is-cauchy-sequence-partial-sum-is-convergent-series-ℝ-Banach-Space :
    is-convergent-series-ℝ-Banach-Space V σ →
    is-inhabited
      ( is-cauchy-sequence-Metric-Space
        ( metric-space-ℝ-Banach-Space V)
        ( partial-sum-series-ℝ-Banach-Space V σ))
  is-cauchy-sequence-partial-sum-is-convergent-series-ℝ-Banach-Space
    (lim , is-lim) =
    map-is-inhabited
      ( is-cauchy-has-limit-modulus-sequence-Metric-Space
        ( metric-space-ℝ-Banach-Space V)
        ( partial-sum-series-ℝ-Banach-Space V σ)
        ( lim))
      ( is-lim)
```

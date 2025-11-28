# Convergent series in real Banach spaces

```agda
module analysis.convergent-series-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.complete-metric-abelian-groups-real-banach-spaces
open import analysis.convergent-series-complete-metric-abelian-groups
open import analysis.convergent-series-metric-abelian-groups
open import analysis.series-real-banach-spaces

open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.real-banach-spaces

open import metric-spaces.cauchy-sequences-metric-spaces
```

</details>

## Idea

A [series](analysis.series-real-banach-spaces.md)
[converges](analysis.convergent-series-metric-abelian-groups.md) in a
[real Banach space](linear-algebra.real-banach-spaces.md) if its partial sums
form a [Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md).

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

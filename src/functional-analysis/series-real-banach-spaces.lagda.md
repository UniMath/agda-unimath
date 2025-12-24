# Series in real Banach spaces

```agda
module functional-analysis.series-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups-normed-real-vector-spaces
open import analysis.series-metric-abelian-groups

open import foundation.universe-levels

open import functional-analysis.real-banach-spaces

open import lists.sequences
```

</details>

## Idea

A
{{#concept "series" Disambiguation="in a real Banach space" Agda=series-ℝ-Banach-Space}}
is a [series](analysis.series-metric-abelian-groups.md) in the
[metric abelian group](analysis.metric-abelian-groups.md)
[associated](analysis.metric-abelian-groups-normed-real-vector-spaces.md) with
the underlying
[normed real vector space](linear-algebra.normed-real-vector-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  where

  series-ℝ-Banach-Space : UU l2
  series-ℝ-Banach-Space =
    series-Metric-Ab
      ( metric-ab-Normed-ℝ-Vector-Space (normed-vector-space-ℝ-Banach-Space V))

  series-terms-ℝ-Banach-Space :
    sequence (type-ℝ-Banach-Space V) → series-ℝ-Banach-Space
  series-terms-ℝ-Banach-Space = series-terms-Metric-Ab

  term-series-ℝ-Banach-Space :
    series-ℝ-Banach-Space → sequence (type-ℝ-Banach-Space V)
  term-series-ℝ-Banach-Space = term-series-Metric-Ab

  partial-sum-series-ℝ-Banach-Space :
    series-ℝ-Banach-Space → sequence (type-ℝ-Banach-Space V)
  partial-sum-series-ℝ-Banach-Space = partial-sum-series-Metric-Ab
```

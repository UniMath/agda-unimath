# Convergent series in the real numbers

```agda
module analysis.convergent-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-complete-metric-abelian-groups
open import analysis.convergent-series-metric-abelian-groups
open import analysis.series-real-numbers

open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.cauchy-sequences-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-additive-group-of-real-numbers
```

</details>

## Idea

A [series of real numbers](analysis.series-real-numbers.md) is
{{#concept "convergent" Disambiguation="series in ℝ" Agda=is-convergent-series-ℝ Agda=convergent-series-ℝ WDID=Q1211057 WD="convergent series"}}
if its partial sums converge in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  is-sum-prop-series-ℝ : ℝ l → Prop l
  is-sum-prop-series-ℝ = is-sum-prop-series-Metric-Ab σ

  is-sum-series-ℝ : ℝ l → UU l
  is-sum-series-ℝ = is-sum-series-Metric-Ab σ

  is-convergent-prop-series-ℝ : Prop (lsuc l)
  is-convergent-prop-series-ℝ =
    is-convergent-prop-series-Metric-Ab σ

  is-convergent-series-ℝ : UU (lsuc l)
  is-convergent-series-ℝ = is-convergent-series-Metric-Ab σ
```

## Properties

### If the partial sums of a series form a Cauchy sequence, the series converges

```agda
module _
  {l : Level}
  (σ : series-ℝ l)
  where

  is-convergent-is-cauchy-sequence-partial-sum-series-ℝ :
    is-cauchy-sequence-ℝ (partial-sum-series-ℝ σ) →
    is-convergent-series-ℝ σ
  is-convergent-is-cauchy-sequence-partial-sum-series-ℝ =
    is-convergent-is-cauchy-sequence-partial-sum-series-Complete-Metric-Ab
      ( complete-metric-ab-add-ℝ l)
      ( σ)
```

## External links

- [Convergent series](https://en.wikipedia.org/wiki/Ratio_test) on Wikipedia

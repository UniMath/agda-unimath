# Series in complete metric abelian groups

```agda
module analysis.series-complete-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.complete-metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import foundation.universe-levels

open import lists.sequences
```

</details>

## Idea

A [series](analysis.series-metric-abelian-groups.md) in a
[complete metric abelian group](analysis.complete-metric-abelian-groups.md) is a
series in the underlying
[metric abelian group](analysis.metric-abelian-groups.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Complete-Metric-Ab l1 l2)
  where

  series-Complete-Metric-Ab : UU l1
  series-Complete-Metric-Ab = series-Metric-Ab (metric-ab-Complete-Metric-Ab G)

  series-terms-Complete-Metric-Ab :
    sequence (type-Complete-Metric-Ab G) → series-Complete-Metric-Ab
  series-terms-Complete-Metric-Ab = series-terms-Metric-Ab

  term-series-Complete-Metric-Ab :
    series-Complete-Metric-Ab → sequence (type-Complete-Metric-Ab G)
  term-series-Complete-Metric-Ab = term-series-Metric-Ab

  partial-sum-series-Complete-Metric-Ab :
    series-Complete-Metric-Ab → sequence (type-Complete-Metric-Ab G)
  partial-sum-series-Complete-Metric-Ab =
    partial-sum-series-Metric-Ab (metric-ab-Complete-Metric-Ab G)
```

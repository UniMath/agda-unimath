# Convergent series in metric abelian groups

```agda
module analysis.convergent-series-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
```

</details>

## Idea

A [series](analysis.series-metric-abelian-groups.md) in a
[metric abelian group](analysis.metric-abelian-groups.md) is
{{#concept "convergent" Disambiguation="series in a metric abelian group" Agda=is-convergent-series-Metric-Ab Agda=convergent-series-Metric-Ab WDID=Q1211057 WD="convergent series"}}
if its [sequence](lists.sequences.md) of partial sums
[converges](metric-spaces.convergent-sequences-metric-spaces.md) in the
associated [metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level} (G : Metric-Ab l1 l2) (σ : series-Metric-Ab G)
  where

  is-convergent-prop-series-Metric-Ab : Prop (l1 ⊔ l2)
  is-convergent-prop-series-Metric-Ab =
    subtype-convergent-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-series-Metric-Ab G σ)

  is-convergent-series-Metric-Ab : UU (l1 ⊔ l2)
  is-convergent-series-Metric-Ab =
    type-Prop is-convergent-prop-series-Metric-Ab

convergent-series-Metric-Ab :
  {l1 l2 : Level} (G : Metric-Ab l1 l2) → UU (l1 ⊔ l2)
convergent-series-Metric-Ab G =
  type-subtype (is-convergent-prop-series-Metric-Ab G)
```

## Properties

```agda
module _
  {l1 l2 : Level} (G : Metric-Ab l1 l2) (σ : convergent-series-Metric-Ab G)
  where

  series-convergent-series-Metric-Ab : series-Metric-Ab G
  series-convergent-series-Metric-Ab = pr1 σ

  partial-sum-convergent-series-Metric-Ab : sequence (type-Metric-Ab G)
  partial-sum-convergent-series-Metric-Ab =
    partial-sum-series-Metric-Ab G series-convergent-series-Metric-Ab
```

## The partial sums of a convergent series have a limit, the sum of the series

```agda
module _
  {l1 l2 : Level} (G : Metric-Ab l1 l2) (σ : convergent-series-Metric-Ab G)
  where

  has-limit-partial-sum-convergent-series-Metric-Ab :
    has-limit-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-convergent-series-Metric-Ab G σ)
  has-limit-partial-sum-convergent-series-Metric-Ab =
    pr2 σ

  sum-convergent-series-Metric-Ab : type-Metric-Ab G
  sum-convergent-series-Metric-Ab =
    limit-has-limit-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-convergent-series-Metric-Ab G σ)
      ( has-limit-partial-sum-convergent-series-Metric-Ab)

  is-limit-partial-sum-convergent-series-Metric-Ab :
    is-limit-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-convergent-series-Metric-Ab G σ)
      ( sum-convergent-series-Metric-Ab)
  is-limit-partial-sum-convergent-series-Metric-Ab =
    is-limit-limit-has-limit-sequence-Metric-Space
      ( metric-space-Metric-Ab G)
      ( partial-sum-convergent-series-Metric-Ab G σ)
      ( has-limit-partial-sum-convergent-series-Metric-Ab)
```

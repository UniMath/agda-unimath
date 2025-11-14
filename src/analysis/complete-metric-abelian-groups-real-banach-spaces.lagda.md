# Complete metric abelian groups of real Banach spaces

```agda
module analysis.complete-metric-abelian-groups-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.complete-metric-abelian-groups
open import analysis.metric-abelian-groups
open import analysis.metric-abelian-groups-normed-real-vector-spaces

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.real-banach-spaces
```

</details>

## Idea

Every [real Banach space](linear-algebra.real-banach-spaces.md) forms a
[complete metric abelian group](analysis.complete-metric-abelian-groups.md)
under addition.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  where

  metric-ab-add-ℝ-Banach-Space : Metric-Ab l2 l1
  metric-ab-add-ℝ-Banach-Space =
    metric-ab-Normed-ℝ-Vector-Space (normed-vector-space-ℝ-Banach-Space V)

  complete-metric-ab-add-ℝ-Banach-Space : Complete-Metric-Ab l2 l1
  complete-metric-ab-add-ℝ-Banach-Space =
    ( metric-ab-add-ℝ-Banach-Space , is-complete-metric-space-ℝ-Banach-Space V)
```

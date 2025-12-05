# The underlying additive complete metric abelian groups of real Banach spaces

```agda
module analysis.additive-complete-metric-abelian-groups-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.complete-metric-abelian-groups
open import analysis.metric-abelian-groups
open import analysis.metric-abelian-groups-normed-real-vector-spaces

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.real-banach-spaces

open import real-numbers.metric-additive-group-of-real-numbers
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

## Properties

### The complete metric abelian group from the reals as a real Banach space equals the standard complete metric abelian group of the reals under addition

```agda
abstract
  eq-complete-metric-ab-ℝ :
    (l : Level) →
    complete-metric-ab-add-ℝ-Banach-Space (real-banach-space-ℝ l) ＝
    complete-metric-ab-add-ℝ l
  eq-complete-metric-ab-ℝ l =
    eq-type-subtype
      ( is-complete-prop-Metric-Ab)
      ( eq-metric-ab-normed-real-vector-space-metric-ab-ℝ l)
```

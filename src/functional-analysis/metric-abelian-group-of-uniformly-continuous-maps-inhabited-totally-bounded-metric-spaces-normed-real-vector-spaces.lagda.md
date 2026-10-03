# Metric abelian groups of uniformly continuous maps from inhabited, totally bounded metric spaces to normed real vector spaces

```agda
module functional-analysis.metric-abelian-group-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups
open import analysis.metric-abelian-groups-of-uniformly-continuous-maps-into-metric-abelian-groups

open import foundation.universe-levels

open import functional-analysis.metric-abelian-groups-normed-real-vector-spaces
open import functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces
open import functional-analysis.supremum-of-norms-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces

open import group-theory.abelian-groups

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.inhabited-totally-bounded-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.metrics-of-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

The
[uniformly continuous maps from an inhabited totally bounded metric space to a normed real vector space](functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces.md)
form a [metric abelian group](analysis.metric-abelian-groups.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (let
    uniformly-continuous-map-X→V =
      uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
        ( X)
        ( V))
  where

  metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    Metric-Ab (l1 ⊔ l2 ⊔ l4 ⊔ l5) (l1 ⊔ l4)
  metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    metric-ab-uniformly-continuous-map-Metric-Ab
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-ab-Normed-ℝ-Vector-Space V)

  ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    Ab (l1 ⊔ l2 ⊔ l4 ⊔ l5)
  ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    ab-Metric-Ab
      ( metric-ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  add-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-X→V → uniformly-continuous-map-X→V →
    uniformly-continuous-map-X→V
  add-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    add-Ab
      ( ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  diff-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-X→V → uniformly-continuous-map-X→V →
    uniformly-continuous-map-X→V
  diff-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    right-subtraction-Ab
      ( ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  zero-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-X→V
  zero-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    zero-Ab
      ( ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  neg-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-X→V → uniformly-continuous-map-X→V
  neg-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    neg-Ab
      ( ab-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
```

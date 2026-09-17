# The real vector spaces of uniformly continuous maps from metric spaces into normed real vector spaces

```agda
module linear-algebra.real-vector-spaces-uniformly-continuous-maps-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups-of-uniformly-continuous-maps-into-metric-abelian-groups

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import functional-analysis.metric-abelian-groups-normed-real-vector-spaces

open import linear-algebra.function-real-vector-spaces
open import linear-algebra.lipschitz-continuity-scalar-multiplication-normed-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-vector-spaces
open import linear-algebra.subsets-left-modules-rings
open import linear-algebra.subspaces-vector-spaces

open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.field-of-real-numbers
open import real-numbers.large-ring-of-real-numbers
```

</details>

## Idea

Given a [metric space](metric-spaces.metric-spaces.md) `X` and a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md), the
[uniformly continuous maps](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from `X` to `V` form a
[real vector space](linear-algebra.real-vector-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (V : Normed-ℝ-Vector-Space l3 l4)
  where

  vector-space-map-metric-space-Normed-ℝ-Vector-Space :
    ℝ-Vector-Space l3 (l1 ⊔ l4)
  vector-space-map-metric-space-Normed-ℝ-Vector-Space =
    function-ℝ-Vector-Space
      ( vector-space-Normed-ℝ-Vector-Space V)
      ( type-Metric-Space X)

  is-uniformly-continuous-const-zero-map-metric-space-Normed-ℝ-Vector-Space :
    is-uniformly-continuous-map-Metric-Space
      ( X)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( λ _ → zero-Normed-ℝ-Vector-Space V)
  is-uniformly-continuous-const-zero-map-metric-space-Normed-ℝ-Vector-Space =
    is-uniformly-continuous-map-const-map-Metric-Space
      ( X)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( zero-Normed-ℝ-Vector-Space V)

  is-closed-under-addition-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space :
    is-closed-under-addition-subset-left-module-Ring
      ( ring-ℝ l3)
      ( vector-space-map-metric-space-Normed-ℝ-Vector-Space)
      ( is-uniformly-continuous-prop-map-Metric-Space
        ( X)
        ( metric-space-Normed-ℝ-Vector-Space V))
  is-closed-under-addition-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space
    f g uc-f uc-g =
    is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
      ( X)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( add-uniformly-continuous-map-Metric-Ab
        ( X)
        ( metric-ab-Normed-ℝ-Vector-Space V)
        ( f , uc-f)
        ( g , uc-g))

  is-closed-under-scalar-multiplication-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space :
    is-closed-under-scalar-multiplication-subset-left-module-Ring
      ( ring-ℝ l3)
      ( vector-space-map-metric-space-Normed-ℝ-Vector-Space)
      ( is-uniformly-continuous-prop-map-Metric-Space
        ( X)
        ( metric-space-Normed-ℝ-Vector-Space V))
  is-closed-under-scalar-multiplication-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space
    c f =
    is-uniformly-continuous-map-comp-Metric-Space
      ( X)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( mul-Normed-ℝ-Vector-Space V c)
      ( f)
      ( is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( mul-Normed-ℝ-Vector-Space V c)
        ( is-lipschitz-left-mul-Normed-ℝ-Vector-Space V c))

  subspace-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space :
    subspace-Vector-Space
      (l1 ⊔ l2 ⊔ l3)
      ( heyting-field-ℝ l3)
      ( vector-space-map-metric-space-Normed-ℝ-Vector-Space)
  subspace-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space =
    ( is-uniformly-continuous-prop-map-Metric-Space
        ( X)
        ( metric-space-Normed-ℝ-Vector-Space V) ,
      is-uniformly-continuous-const-zero-map-metric-space-Normed-ℝ-Vector-Space ,
      is-closed-under-addition-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space ,
      is-closed-under-scalar-multiplication-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space)

  vector-space-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space :
    ℝ-Vector-Space l3 (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  vector-space-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space =
    vector-space-subspace-Vector-Space
      ( heyting-field-ℝ l3)
      ( vector-space-map-metric-space-Normed-ℝ-Vector-Space)
      ( subspace-is-uniformly-continuous-map-metric-space-Normed-ℝ-Vector-Space)
```

# The supremum norm on maps from inhabited totally bounded metric spaces to normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.supremum-of-norms-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import functional-analysis.metric-space-of-uniformly-continuous-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.inhabited-totally-bounded-metric-spaces
open import metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.inhabited-totally-bounded-subsets-nonnegative-real-numbers
open import real-numbers.metric-space-of-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.suprema-families-nonnegative-real-numbers
```

</details>

## Idea

Given a
[uniformly continuous map](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
`f` from an
[inhabited totally bounded metric space](metric-spaces.inhabited-totally-bounded-metric-spaces.md)
`X` to a [normed real vector space](linear-algebra.normed-real-vector-spaces.md)
`V`, the family of
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) `x ↦ ∥f x∥`
has a [supremum](real-numbers.suprema-families-nonnegative-real-numbers.md),
generally denoted $\lVert f \rVert_X$.

We will call this the
{{#concept "supremum norm" WDID=Q1202673 WD="uniform norm" Disambiguation="on uniformly continuous maps from inhabited totally bounded metric spaces to normed real vector spaces"}},
as it
[is actually a norm on such maps](functional-analysis.supremum-norm-maps-inhabited-totally-bounded-metric-spaces-normed-real-vector-spaces.md),

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (X : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  (V : Normed-ℝ-Vector-Space l4 l5)
  (f :
    uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space
      ( X)
      ( V))
  where

  uniformly-continuous-map-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-ℝ⁰⁺ l4)
  uniformly-continuous-map-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    comp-uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-ℝ⁰⁺ l4)
      ( uniformly-continuous-map-nonnegative-norm-Normed-ℝ-Vector-Space V)
      ( f)

  nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    type-inhabited-totally-bounded-Metric-Space X → ℝ⁰⁺ l4
  nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    map-uniformly-continuous-map-Metric-Space
      ( metric-space-inhabited-totally-bounded-Metric-Space X)
      ( metric-space-ℝ⁰⁺ l4)
      ( uniformly-continuous-map-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  abstract
    has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
      has-supremum-family-ℝ⁰⁺
        ( l4)
        ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
    has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
      has-supremum-has-supremum-im-ℝ⁰⁺
        ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
        ( has-supremum-inhabited-totally-bounded-subset-ℝ⁰⁺
          ( im-uniformly-continuous-map-inhabited-totally-bounded-Metric-Space
            ( X)
            ( metric-space-ℝ⁰⁺ l4)
            ( uniformly-continuous-map-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)))

  sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    ℝ⁰⁺ l4
  sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    pr1
      ( has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  real-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    ℝ l4
  real-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    real-ℝ⁰⁺
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)

  is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space :
    is-supremum-family-ℝ⁰⁺
      ( nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
      ( sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
  is-supremum-sup-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space =
    pr2
      ( has-supremum-nonnegative-norm-map-uniformly-continuous-map-inhabited-totally-bounded-metric-space-Normed-ℝ-Vector-Space)
```

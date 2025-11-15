# Metric abelian groups of normed real vector spaces

```agda
module analysis.metric-abelian-groups-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations

open import real-numbers.dedekind-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.large-additive-group-of-real-numbers
open import real-numbers.metric-additive-group-of-real-numbers
```

</details>

## Idea

A [normed](linear-algebra.normed-real-vector-spaces.md)
[real vector space](linear-algebra.real-vector-spaces.md) forms a
[metric abelian group](analysis.metric-abelian-groups.md) under addition.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  ab-metric-ab-Normed-ℝ-Vector-Space : Ab l2
  ab-metric-ab-Normed-ℝ-Vector-Space = ab-Normed-ℝ-Vector-Space V

  type-metric-ab-Normed-ℝ-Vector-Space : UU l2
  type-metric-ab-Normed-ℝ-Vector-Space = type-Normed-ℝ-Vector-Space V

  pseudometric-structure-metric-ab-Normed-ℝ-Vector-Space :
    Pseudometric-Structure l1 type-metric-ab-Normed-ℝ-Vector-Space
  pseudometric-structure-metric-ab-Normed-ℝ-Vector-Space =
    pseudometric-structure-Metric-Space (metric-space-Normed-ℝ-Vector-Space V)

  pseudometric-space-metric-ab-Normed-ℝ-Vector-Space :
    Pseudometric-Space l2 l1
  pseudometric-space-metric-ab-Normed-ℝ-Vector-Space =
    pseudometric-Metric-Space (metric-space-Normed-ℝ-Vector-Space V)

  metric-ab-Normed-ℝ-Vector-Space : Metric-Ab l2 l1
  metric-ab-Normed-ℝ-Vector-Space =
    ( ab-metric-ab-Normed-ℝ-Vector-Space ,
      pseudometric-structure-metric-ab-Normed-ℝ-Vector-Space ,
      is-extensional-pseudometric-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V) ,
      is-isometry-neg-Normed-ℝ-Vector-Space V ,
      is-isometry-left-add-Normed-ℝ-Vector-Space V)
```

## Properties

### The metric abelian group associated with `ℝ` as a normed vector space over `ℝ` is equal to the metric additive group of `ℝ`

```agda
abstract
  eq-metric-ab-normed-real-vector-space-metric-ab-ℝ :
    (l : Level) →
    metric-ab-Normed-ℝ-Vector-Space (normed-real-vector-space-ℝ l) ＝
    metric-ab-add-ℝ l
  eq-metric-ab-normed-real-vector-space-metric-ab-ℝ l =
    eq-pair-eq-fiber
      ( eq-type-subtype
        ( λ M → is-metric-ab-prop-Ab-Pseudometric-Structure (ab-add-ℝ l) M)
        ( eq-type-subtype
          ( is-pseudometric-prop-Rational-Neighborhood-Relation (ℝ l))
          ( eq-Eq-Rational-Neighborhood-Relation _ _
            ( λ d x y → inv-iff (neighborhood-iff-leq-dist-ℝ d x y)))))
```

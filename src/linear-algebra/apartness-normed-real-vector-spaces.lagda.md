# Apartness in normed real vector spaces

```agda
module linear-algebra.apartness-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.tight-apartness-relations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.apartness-located-metric-spaces

open import real-numbers.inequality-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

Two points in a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) are
{{#concept "apart" Disambiguation="in a normed real vector space" Agda=apart-Normed-ℝ-Vector-Space}}
if the distance between them is
[positive](real-numbers.positive-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  apart-prop-Normed-ℝ-Vector-Space :
    Relation-Prop l1 (type-Normed-ℝ-Vector-Space V)
  apart-prop-Normed-ℝ-Vector-Space v w =
    is-positive-prop-ℝ (dist-Normed-ℝ-Vector-Space V v w)

  apart-Normed-ℝ-Vector-Space :
    Relation l1 (type-Normed-ℝ-Vector-Space V)
  apart-Normed-ℝ-Vector-Space =
    type-Relation-Prop apart-prop-Normed-ℝ-Vector-Space
```

## Properties

### Two elements are apart in a normed real vector space if and only if they are apart in the corresponding located metric space

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (v w : type-Normed-ℝ-Vector-Space V)
  where abstract

  apart-located-metric-space-apart-Normed-ℝ-Vector-Space :
    apart-Normed-ℝ-Vector-Space V v w →
    apart-Located-Metric-Space
      ( located-metric-space-Normed-ℝ-Vector-Space V)
      ( v)
      ( w)
  apart-located-metric-space-apart-Normed-ℝ-Vector-Space =
    exists-not-le-positive-rational-is-positive-ℝ
      ( dist-Normed-ℝ-Vector-Space V v w)

  apart-apart-located-metric-space-Normed-ℝ-Vector-Space :
    apart-Located-Metric-Space
      ( located-metric-space-Normed-ℝ-Vector-Space V)
      ( v)
      ( w) →
    apart-Normed-ℝ-Vector-Space V v w
  apart-apart-located-metric-space-Normed-ℝ-Vector-Space =
    is-positive-exists-not-le-positive-rational-ℝ
      ( dist-Normed-ℝ-Vector-Space V v w)
```

### Apartness in a normed real vector space is an apartness relation

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    antirefl-apart-Normed-ℝ-Vector-Space :
      (v : type-Normed-ℝ-Vector-Space V) →
      ¬ (apart-Normed-ℝ-Vector-Space V v v)
    antirefl-apart-Normed-ℝ-Vector-Space v =
      is-not-positive-is-zero-ℝ
        ( dist-Normed-ℝ-Vector-Space V v v)
        ( refl-dist-Normed-ℝ-Vector-Space V v)

    symmetric-apart-Normed-ℝ-Vector-Space :
      (v w : type-Normed-ℝ-Vector-Space V) →
      apart-Normed-ℝ-Vector-Space V v w → apart-Normed-ℝ-Vector-Space V w v
    symmetric-apart-Normed-ℝ-Vector-Space v w =
      tr is-positive-ℝ (symmetric-dist-Normed-ℝ-Vector-Space V v w)

    cotransitive-apart-Normed-ℝ-Vector-Space :
      (v w x : type-Normed-ℝ-Vector-Space V) →
      apart-Normed-ℝ-Vector-Space V v x →
      disjunction-type
        ( apart-Normed-ℝ-Vector-Space V v w)
        ( apart-Normed-ℝ-Vector-Space V w x)
    cotransitive-apart-Normed-ℝ-Vector-Space v w x 0<dvx =
      map-disjunction
        ( apart-apart-located-metric-space-Normed-ℝ-Vector-Space V v w)
        ( apart-apart-located-metric-space-Normed-ℝ-Vector-Space V w x)
        ( is-cotransitive-apart-Located-Metric-Space
          ( located-metric-space-Normed-ℝ-Vector-Space V)
          ( v)
          ( w)
          ( x)
          ( apart-located-metric-space-apart-Normed-ℝ-Vector-Space V v x 0<dvx))

  is-apartness-relation-apart-Normed-ℝ-Vector-Space :
    is-apartness-relation (apart-prop-Normed-ℝ-Vector-Space V)
  is-apartness-relation-apart-Normed-ℝ-Vector-Space =
    ( antirefl-apart-Normed-ℝ-Vector-Space ,
      symmetric-apart-Normed-ℝ-Vector-Space ,
      cotransitive-apart-Normed-ℝ-Vector-Space)

  apartness-relation-Normed-ℝ-Vector-Space :
    Apartness-Relation l1 (type-Normed-ℝ-Vector-Space V)
  apartness-relation-Normed-ℝ-Vector-Space =
    ( apart-prop-Normed-ℝ-Vector-Space V ,
      is-apartness-relation-apart-Normed-ℝ-Vector-Space)
```

### Apartness in a normed real vector space is a tight apartness relation

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    is-tight-apart-Normed-ℝ-Vector-Space :
      (v w : type-Normed-ℝ-Vector-Space V) →
      ¬ apart-Normed-ℝ-Vector-Space V v w →
      v ＝ w
    is-tight-apart-Normed-ℝ-Vector-Space v w H =
      is-extensional-dist-Normed-ℝ-Vector-Space V v w
        ( sim-sim-leq-ℝ
          ( leq-not-le-ℝ zero-ℝ (dist-Normed-ℝ-Vector-Space V v w) H ,
            is-nonnegative-dist-Normed-ℝ-Vector-Space V v w))

  tight-apartness-relation-Normed-ℝ-Vector-Space :
    Tight-Apartness-Relation l1 (type-Normed-ℝ-Vector-Space V)
  tight-apartness-relation-Normed-ℝ-Vector-Space =
    ( apartness-relation-Normed-ℝ-Vector-Space V ,
      is-tight-apart-Normed-ℝ-Vector-Space)
```

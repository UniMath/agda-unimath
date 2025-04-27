# The metric space of cauchy approximations in a complete metric space

```agda
module metric-spaces.metric-space-of-cauchy-approximations-in-a-complete-metric-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-in-a-metric-space
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

The type of
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
a [complete metric space](metric-spaces.complete-metric-spaces.md) `A` inherits
the
[metric structure](metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space.md)
of the cauchy sequences in the underlying metric space.

This is the
{{#concept "metric space of cauchy approximations" Disambiguation="in a complete metric space" Agda=metric-space-cauchy-approximations-Complete-Metric-Space}}
in a saturated complete metric space.

In a complete metric space, all Cauchy approximations are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
and the corresponding map into the
[metric space of convergent Cauchy approximations](metric-spaces.metric-space-of-convergent-cauchy-approximations-in-a-metric-space.md)
is an [isometry](metric-spaces.isometries-metric-spaces.md).

## Definitions

### The metric space of cauchy approximations in a complete metric space

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  metric-space-of-cauchy-approximations-Complete-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  metric-space-of-cauchy-approximations-Complete-Metric-Space =
    metric-space-of-cauchy-approximations-Metric-Space
      ( metric-space-Complete-Metric-Space A)
```

## Properties

### The map from a cauchy approximation in a metric space to its convergent approximation is an isometry

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  is-isometry-convergent-cauchy-approximation-Complete-Metric-Space :
    is-isometry-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( convergent-cauchy-approximation-Complete-Metric-Space A)
  is-isometry-convergent-cauchy-approximation-Complete-Metric-Space d x y =
    (id , id)

  isometry-convergent-cauchy-approximation-Complete-Metric-Space :
    isometry-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
  isometry-convergent-cauchy-approximation-Complete-Metric-Space =
    convergent-cauchy-approximation-Complete-Metric-Space A ,
    is-isometry-convergent-cauchy-approximation-Complete-Metric-Space
```

### The metric space of cauchy approximations in a complete metric space is equal to the metric space of convergent cauchy approximations in its underlying metric space

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  eq-metric-space-convergent-cauchy-approximations-Complete-Metric-Space :
    ( metric-space-of-cauchy-approximations-Complete-Metric-Space A) ＝
    ( metric-space-of-convergent-cauchy-approximations-Metric-Space
      ( metric-space-Complete-Metric-Space A))
  eq-metric-space-convergent-cauchy-approximations-Complete-Metric-Space =
    eq-isometric-equiv-Metric-Space'
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( convergent-cauchy-approximation-Complete-Metric-Space A ,
        is-equiv-convergent-cauchy-approximation-Complete-Metric-Space A ,
        is-isometry-convergent-cauchy-approximation-Complete-Metric-Space A)
```

### The map from a cauchy approximation in a metric space to its convergent approximation is short

```agda
module _
  {l1 l2 : Level} (A : Complete-Metric-Space l1 l2)
  where

  short-convergent-cauchy-approximation-Complete-Metric-Space :
    short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
  short-convergent-cauchy-approximation-Complete-Metric-Space =
    short-isometry-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( isometry-convergent-cauchy-approximation-Complete-Metric-Space A)

  is-short-convergent-cauchy-approximation-Complete-Metric-Space :
    is-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( convergent-cauchy-approximation-Complete-Metric-Space A)
  is-short-convergent-cauchy-approximation-Complete-Metric-Space =
    is-short-map-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Complete-Metric-Space A))
      ( short-convergent-cauchy-approximation-Complete-Metric-Space)
```

# The metric space of cauchy approximations in a saturated complete metric space

```agda
module metric-spaces.metric-space-of-cauchy-approximations-in-a-saturated-complete-metric-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.metric-space-of-cauchy-approximations-in-a-complete-metric-space
open import metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-in-a-metric-space
open import metric-spaces.metric-spaces
open import metric-spaces.saturated-complete-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The type of
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
a
[saturated complete metric space](metric-spaces.saturated-complete-metric-spaces.md)
`A` inherits the
[metric structure](metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space.md)
of the cauchy sequences in the underlying metric space.

This is the
{{#concept "metric space of cauchy approximations" Disambiguation="in a saturated complete metric space" Agda=metric-space-cauchy-approximations-Saturated-Complete-Metric-Space}}
in a saturated complete metric space.

In a saturated complete metric space, all Cauchy approximations are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
and the map from a Cauchy approximation to its limit is
[short](metric-spaces.short-functions-metric-spaces.md).

## Definitions

### The metric space of cauchy approximations in a saturated complete metric space

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  metric-space-cauchy-approximations-Saturated-Complete-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  metric-space-cauchy-approximations-Saturated-Complete-Metric-Space =
    metric-space-cauchy-approximations-Metric-Space
      ( metric-space-Saturated-Complete-Metric-Space A)
```

## Properties

### The map from a cauchy approximation in a saturated metric space to its limit is short

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  short-limit-cauchy-approximation-Saturated-Complete-Metric-Space :
    short-function-Metric-Space
      ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space A)
      ( metric-space-Saturated-Complete-Metric-Space A)
  short-limit-cauchy-approximation-Saturated-Complete-Metric-Space =
    comp-short-function-Metric-Space
      ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space A)
      ( metric-space-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A))
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( short-limit-convergent-cauchy-approximation-is-saturated-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
        ( is-saturated-metric-space-Saturated-Complete-Metric-Space A))
      ( short-convergent-cauchy-approximation-Complete-Metric-Space
        ( complete-metric-space-Saturated-Complete-Metric-Space A))

  is-short-limit-cauchy-approximation-Saturated-Complete-Metric-Space :
    is-short-function-Metric-Space
      ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space A)
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( limit-cauchy-approximation-Saturated-Complete-Metric-Space A)
  is-short-limit-cauchy-approximation-Saturated-Complete-Metric-Space =
    is-short-map-short-function-Metric-Space
      ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space A)
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( short-limit-cauchy-approximation-Saturated-Complete-Metric-Space)
```

# The saturated complete metric space of cauchy approximations in a saturated complete metric space

```agda
module metric-spaces.saturated-complete-metric-space-of-cauchy-approximations-in-a-saturated-complete-metric-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.metric-space-of-cauchy-approximations-in-a-complete-metric-space
open import metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-in-a-metric-space
open import metric-spaces.metric-spaces
open import metric-spaces.saturated-complete-metric-spaces
open import metric-spaces.saturated-metric-spaces
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

### The metric space of Cauchy approximations in a saturated complete metric space

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

### The metric space of Cauchy approximations in a saturated complete metric space is saturated

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  is-saturated-metric-space-cauchy-approximations-Saturated-Complete-Metric-Space :
    is-saturated-Metric-Space
      (metric-space-cauchy-approximations-Saturated-Complete-Metric-Space A)
  is-saturated-metric-space-cauchy-approximations-Saturated-Complete-Metric-Space =
    is-saturated-metric-space-cauchy-approximations-is-saturated-Metric-Space
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( is-saturated-metric-space-Saturated-Complete-Metric-Space A)
```

### The map from a Cauchy approximation in a saturated complete metric space to its limit is short

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

### The metric space of Cauchy approximations in a saturated complete metric space is complete

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  is-complete-metric-space-cauchy-approximations-Saturated-Complete-Metric-Space :
    is-complete-Metric-Space
      ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space A)
  is-complete-metric-space-cauchy-approximations-Saturated-Complete-Metric-Space
    U = lim-U , is-limit-lim-U
    where

    swap-U :
      ℚ⁺ →
      cauchy-approximation-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
    swap-U η =
      ( λ ε →
        map-cauchy-approximation-Metric-Space
          ( metric-space-Saturated-Complete-Metric-Space A)
          ( map-cauchy-approximation-Metric-Space
            ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space
              ( A))
            ( U)
            ( ε))
            ( η)) ,
      ( λ ε δ →
        is-cauchy-approximation-map-cauchy-approximation-Metric-Space
          ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space
            ( A))
          ( U)
          ( ε)
          ( δ)
          ( η))

    map-lim-U : ℚ⁺ → type-Saturated-Complete-Metric-Space A
    map-lim-U η =
      limit-cauchy-approximation-Complete-Metric-Space
        ( complete-metric-space-Saturated-Complete-Metric-Space A)
        ( swap-U η)

    is-cauchy-map-lim-U :
      is-cauchy-approximation-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
        ( map-lim-U)
    is-cauchy-map-lim-U ε δ =
      is-short-limit-cauchy-approximation-Saturated-Complete-Metric-Space
        ( A)
        ( ε +ℚ⁺ δ)
        ( swap-U ε)
        ( swap-U δ)
        ( λ η →
          is-cauchy-approximation-map-cauchy-approximation-Metric-Space
            ( metric-space-Saturated-Complete-Metric-Space A)
            ( map-cauchy-approximation-Metric-Space
              ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space
                ( A))
              ( U)
              ( η))
            ( ε)
            ( δ))

    lim-U :
      cauchy-approximation-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
    lim-U = map-lim-U , is-cauchy-map-lim-U

    is-limit-lim-U :
      is-limit-cauchy-approximation-Metric-Space
        ( metric-space-cauchy-approximations-Saturated-Complete-Metric-Space A)
        ( U)
        ( lim-U)
    is-limit-lim-U ε δ η =
      is-limit-limit-cauchy-approximation-Complete-Metric-Space
        ( complete-metric-space-Saturated-Complete-Metric-Space A)
        ( swap-U η)
        ( ε)
        ( δ)
```

### The saturated complete metric space of Cauchy approximations in a saturated complete metric space

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  saturated-complete-metric-space-cauchy-approximations-Saturated-Metric-Space :
    Saturated-Complete-Metric-Space (l1 ⊔ l2) l2
  pr1
    saturated-complete-metric-space-cauchy-approximations-Saturated-Metric-Space
    = metric-space-cauchy-approximations-Saturated-Complete-Metric-Space A
  pr2
    saturated-complete-metric-space-cauchy-approximations-Saturated-Metric-Space
    =
    ( is-complete-metric-space-cauchy-approximations-Saturated-Complete-Metric-Space
      A) ,
    ( is-saturated-metric-space-cauchy-approximations-Saturated-Complete-Metric-Space
      A)
```

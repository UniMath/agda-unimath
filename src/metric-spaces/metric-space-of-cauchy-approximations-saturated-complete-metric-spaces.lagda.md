# The metric space of Cauchy approximations in a saturated complete metric space

```agda
module metric-spaces.metric-space-of-cauchy-approximations-saturated-complete-metric-spaces where
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
open import metric-spaces.metric-space-of-cauchy-approximations-complete-metric-spaces
open import metric-spaces.metric-space-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-metric-spaces
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
[metric structure](metric-spaces.metric-space-of-cauchy-approximations-metric-spaces.md)
of the Cauchy approximations in the underlying metric space; this is the
{{#concept "saturated complete metric space of Cauchy approximations" Disambiguation="in a saturated complete metric space" Agda=saturated-complete-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space}}
in a saturated complete metric space.

All Cauchy approximations in a saturated complete metric space are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
and the map from a Cauchy approximation to its limit is
[short](metric-spaces.short-functions-metric-spaces.md).

## Definitions

### The metric space of Cauchy approximations in a saturated complete metric space

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space =
    metric-space-of-cauchy-approximations-Metric-Space
      ( metric-space-Saturated-Complete-Metric-Space A)
```

## Properties

### The metric space of Cauchy approximations in a saturated complete metric space is saturated

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  is-saturated-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space :
    is-saturated-Metric-Space
      (metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space A)
  is-saturated-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space =
    is-saturated-metric-space-of-cauchy-approximations-is-saturated-Metric-Space
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
      ( metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space A)
      ( metric-space-Saturated-Complete-Metric-Space A)
  short-limit-cauchy-approximation-Saturated-Complete-Metric-Space =
    comp-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space A)
      ( metric-space-of-convergent-cauchy-approximations-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A))
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( short-limit-convergent-cauchy-approximation-is-saturated-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
        ( is-saturated-metric-space-Saturated-Complete-Metric-Space A))
      ( short-convergent-cauchy-approximation-Complete-Metric-Space
        ( complete-metric-space-Saturated-Complete-Metric-Space A))

  is-short-limit-cauchy-approximation-Saturated-Complete-Metric-Space :
    is-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space A)
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( limit-cauchy-approximation-Saturated-Complete-Metric-Space A)
  is-short-limit-cauchy-approximation-Saturated-Complete-Metric-Space =
    is-short-map-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space A)
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( short-limit-cauchy-approximation-Saturated-Complete-Metric-Space)
```

### The metric space of Cauchy approximations in a saturated complete metric space is complete

Given a Cauchy approximation of Cauchy approximations `U : ℚ⁺ → ℚ⁺ → A` in a
saturated complete metric space `A`, we construct its limit as follows:

1. for any `η : ℚ⁺`, the partial application `ε ↦ U ε η` is a Cauchy
   approximation in `A`;
2. since `A` is complete, it converges to some `lim-η : A`;
3. since `A` is saturated, the assignment `η ↦ lim-η` is a Cauchy approximation
   in `A`;
4. by construction it's a limit of `U` in the space of Cauchy approximations.

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  (U : cauchy-approximation-Metric-Space
    ( metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space A))
  where

  map-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space :
    ℚ⁺ → type-Saturated-Complete-Metric-Space A
  map-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space
    η =
    limit-cauchy-approximation-Complete-Metric-Space
      ( complete-metric-space-Saturated-Complete-Metric-Space A)
      ( swap-cauchy-approximation-cauchy-approximations-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
        ( U)
        ( η))

  is-cauchy-map-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space :
    is-cauchy-approximation-Metric-Space
      ( metric-space-Saturated-Complete-Metric-Space A)
      ( map-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space)
  is-cauchy-map-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space
    ε δ =
    is-short-limit-cauchy-approximation-Saturated-Complete-Metric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( swap-cauchy-approximation-cauchy-approximations-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
        ( U)
        ( ε))
      ( swap-cauchy-approximation-cauchy-approximations-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
        ( U)
        ( δ))
      ( λ η →
        is-cauchy-approximation-map-cauchy-approximation-Metric-Space
          ( metric-space-Saturated-Complete-Metric-Space A)
          ( map-cauchy-approximation-Metric-Space
            ( metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space
              ( A))
            ( U)
            ( η))
          ( ε)
          ( δ))

  lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space :
    cauchy-approximation-Metric-Space
      (metric-space-Saturated-Complete-Metric-Space A)
  lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space
    =
    map-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space ,
    is-cauchy-map-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space

  is-limit-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space
        ( A))
      ( U)
      ( lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space)
  is-limit-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space
    ε δ η =
    is-limit-limit-cauchy-approximation-Complete-Metric-Space
      ( complete-metric-space-Saturated-Complete-Metric-Space A)
      ( swap-cauchy-approximation-cauchy-approximations-Metric-Space
        ( metric-space-Saturated-Complete-Metric-Space A)
        ( U)
        ( η))
      ( ε)
      ( δ)
```

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  is-complete-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space :
    is-complete-Metric-Space
      ( metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space A)
  is-complete-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space
    U =
    ( lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space
      ( A)
      ( U)) ,
    ( is-limit-lim-cauchy-approximation-cauchy-approximations-Saturated-Complete-Metric-Space
      ( A)
      ( U))
```

### The saturated complete metric space of Cauchy approximations in a saturated complete metric space

```agda
module _
  {l1 l2 : Level} (A : Saturated-Complete-Metric-Space l1 l2)
  where

  saturated-complete-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space :
    Saturated-Complete-Metric-Space (l1 ⊔ l2) l2
  pr1
    saturated-complete-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space
    = metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space A
  pr2
    saturated-complete-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space
    =
    ( is-complete-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space
      A) ,
    ( is-saturated-metric-space-of-cauchy-approximations-Saturated-Complete-Metric-Space
      A)
```

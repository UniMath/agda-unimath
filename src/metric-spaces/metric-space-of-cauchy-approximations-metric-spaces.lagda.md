# The metric space of Cauchy approximations in a metric space

```agda
module metric-spaces.metric-space-of-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.saturated-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The type of
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
a [metric space](metric-spaces.metric-spaces.md) `A` inherits the
[metric substructure](metric-spaces.subspaces-metric-spaces.md) of the constant
[product structure](metric-spaces.dependent-products-metric-spaces.md) over `A`.

This is the
{{#concept "metric space of Cauchy approximations" Disambiguation="in a metric space" Agda=metric-space-of-cauchy-approximations-Metric-Space}}
in a metric space.

## Definitions

### The metric space of Cauchy approximations in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  metric-space-of-cauchy-approximations-Metric-Space : Metric-Space (l1 ⊔ l2) l2
  metric-space-of-cauchy-approximations-Metric-Space =
    subspace-Metric-Space
      ( Π-Metric-Space ℚ⁺ (λ _ → A))
      ( is-cauchy-approximation-prop-Metric-Space A)
```

## Properties

### The metric space of Cauchy approximations in a saturated metric space is saturated

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2) (H : is-saturated-Metric-Space A)
  where

  is-saturated-metric-space-of-cauchy-approximations-is-saturated-Metric-Space :
    is-saturated-Metric-Space
      (metric-space-of-cauchy-approximations-Metric-Space A)
  is-saturated-metric-space-of-cauchy-approximations-is-saturated-Metric-Space =
    is-saturated-subspace-is-saturated-Metric-Space
      ( Π-Metric-Space ℚ⁺ (λ _ → A))
      ( is-saturated-Π-is-saturated-Metric-Space ℚ⁺ (λ _ → A) (λ _ → H))
      ( is-cauchy-approximation-prop-Metric-Space A)
```

### The action of short maps on Cauchy approximations is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  where

  is-short-map-short-function-cauchy-approximation-Metric-Space :
    is-short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A)
      ( metric-space-of-cauchy-approximations-Metric-Space B)
      ( map-short-function-cauchy-approximation-Metric-Space A B f)
  is-short-map-short-function-cauchy-approximation-Metric-Space ε x y Nxy δ =
    is-short-map-short-function-Metric-Space A B f ε
      ( map-cauchy-approximation-Metric-Space A x δ)
      ( map-cauchy-approximation-Metric-Space A y δ)
      ( Nxy δ)

  short-map-short-function-cauchy-approximation-Metric-Space :
    short-function-Metric-Space
      ( metric-space-of-cauchy-approximations-Metric-Space A)
      ( metric-space-of-cauchy-approximations-Metric-Space B)
  short-map-short-function-cauchy-approximation-Metric-Space =
    map-short-function-cauchy-approximation-Metric-Space A B f ,
    is-short-map-short-function-cauchy-approximation-Metric-Space
```

### The partial application of a Cauchy approximation of Cauchy approximations is a Cauchy approximation

```agda
module _
  { l1 l2 : Level} (A : Metric-Space l1 l2)
  ( U : cauchy-approximation-Metric-Space
    ( metric-space-of-cauchy-approximations-Metric-Space A))
  where

  swap-cauchy-approximation-cauchy-approximations-Metric-Space :
    ℚ⁺ → cauchy-approximation-Metric-Space A
  swap-cauchy-approximation-cauchy-approximations-Metric-Space
    η =
    ( λ ε →
      map-cauchy-approximation-Metric-Space
        ( A)
        ( map-cauchy-approximation-Metric-Space
          ( metric-space-of-cauchy-approximations-Metric-Space A)
          ( U)
          ( ε))
          ( η)) ,
    ( λ ε δ →
      is-cauchy-approximation-map-cauchy-approximation-Metric-Space
        ( metric-space-of-cauchy-approximations-Metric-Space A)
        ( U)
        ( ε)
        ( δ)
        ( η))
```

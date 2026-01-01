# The metric space of maps between metric spaces

```agda
module metric-spaces.metric-space-of-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

[Maps](metric-spaces.maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) inherit the
[product metric structure](metric-spaces.dependent-products-metric-spaces.md) of
their codomain. This defines the
{{#concept "metric space of maps between metric spaces" Agda=metric-space-of-maps-Metric-Space}}.

## Definitions

### The metric space of maps between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-of-maps-Metric-Space : Metric-Space (l1 ⊔ l1') (l1 ⊔ l2')
  metric-space-of-maps-Metric-Space =
    Π-Metric-Space (type-Metric-Space A) (λ _ → B)
```

## Properties

### The partial applications of a Cauchy approximation of maps form a Cauchy approximation

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  ( f :
    cauchy-approximation-Metric-Space
      ( metric-space-of-maps-Metric-Space A B))
  ( x : type-Metric-Space A)
  where

  ev-cauchy-approximation-map-Metric-Space :
    cauchy-approximation-Metric-Space B
  ev-cauchy-approximation-map-Metric-Space =
    ev-cauchy-approximation-Π-Metric-Space
      ( type-Metric-Space A)
      ( λ _ → B)
      ( f)
      ( x)
```

### A map is the limit of a Cauchy approximation of maps if and only if it is the pointwise limit of its partial applications

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  ( f :
    cauchy-approximation-Metric-Space
      ( metric-space-of-maps-Metric-Space A B))
  ( g : map-Metric-Space A B)
  where

  is-pointwise-limit-is-limit-cauchy-approximation-map-Metric-Space :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-of-maps-Metric-Space A B)
      ( f)
      ( g) →
    (x : type-Metric-Space A) →
    is-limit-cauchy-approximation-Metric-Space
      ( B)
      ( ev-cauchy-approximation-map-Metric-Space A B f x)
      ( g x)
  is-pointwise-limit-is-limit-cauchy-approximation-map-Metric-Space =
    is-pointwise-limit-is-limit-cauchy-approximation-Π-Metric-Space
      ( type-Metric-Space A)
      ( λ _ → B)
      ( f)
      ( g)

  is-limit-is-pointwise-limit-cauchy-approximation-map-Metric-Space :
    ( (x : type-Metric-Space A) →
      is-limit-cauchy-approximation-Metric-Space
        ( B)
        ( ev-cauchy-approximation-map-Metric-Space A B f x)
        ( g x)) →
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-of-maps-Metric-Space A B)
      ( f)
      ( g)
  is-limit-is-pointwise-limit-cauchy-approximation-map-Metric-Space =
    is-limit-is-pointwise-limit-cauchy-approximation-Π-Metric-Space
      ( type-Metric-Space A)
      ( λ _ → B)
      ( f)
      ( g)
```

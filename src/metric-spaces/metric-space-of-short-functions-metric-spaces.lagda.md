# The metric space of short functions between metric spaces

```agda
module metric-spaces.metric-space-of-short-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.metric-space-of-functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

[Short functions](metric-spaces.short-functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) inherit the
[metric subspace](metric-spaces.subspaces-metric-spaces.md) structure of the
[function metric space](metric-spaces.metric-space-of-functions-metric-spaces.md).
This defines the
{{#concept "metric space of short functions between metric spaces" Agda=metric-space-of-short-functions-Metric-Space}}.

## Definitions

### The metric space of short functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-of-short-functions-Metric-Space :
    Metric-Space (l1 ⊔ l2 ⊔ l1' ⊔ l2') (l1 ⊔ l2')
  metric-space-of-short-functions-Metric-Space =
    subspace-Metric-Space
      ( metric-space-of-functions-Metric-Space A B)
      ( is-short-function-prop-Metric-Space A B)
```

### Mapping a short function of short functions

```agda
module _
  { lx lx' ly ly' lz lz' : Level}
  ( X : Metric-Space lx lx') (Y : Metric-Space ly ly') (Z : Metric-Space lz lz')
  ( f :
    short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z))
  where

  map²-short-function-Metric-Space :
    type-Metric-Space X →
    type-Metric-Space Y →
    type-Metric-Space Z
  map²-short-function-Metric-Space =
    ( map-short-function-Metric-Space Y Z) ∘
    ( map-short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z)
      ( f))

  is-short-map²-short-function-Metric-Space :
    (x : type-Metric-Space X) →
    is-short-function-Metric-Space
      ( Y)
      ( Z)
      ( map²-short-function-Metric-Space x)
  is-short-map²-short-function-Metric-Space =
    ( is-short-map-short-function-Metric-Space Y Z) ∘
    ( map-short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z)
      ( f))

  short-map²-short-function-Metric-Space :
    (x : type-Metric-Space X) → short-function-Metric-Space Y Z
  short-map²-short-function-Metric-Space x =
    map²-short-function-Metric-Space x ,
    is-short-map²-short-function-Metric-Space x

  is-short-short-map²-short-function-Metric-Space :
    is-short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z)
      ( short-map²-short-function-Metric-Space)
  is-short-short-map²-short-function-Metric-Space =
    is-short-map-short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z)
      ( f)

  short-short-map²-short-function-Metric-Space :
    short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z)
  short-short-map²-short-function-Metric-Space =
    short-map²-short-function-Metric-Space ,
    is-short-short-map²-short-function-Metric-Space

  eq-short-short-map²-short-map-function-Metric-Space :
    short-short-map²-short-function-Metric-Space ＝ f
  eq-short-short-map²-short-map-function-Metric-Space =
    refl
```

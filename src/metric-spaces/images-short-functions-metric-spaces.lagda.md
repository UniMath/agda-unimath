# Images of metric spaces under short functions

```agda
module metric-spaces.images-short-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.images
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.images-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

Given a [short function](metric-spaces.short-functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) `f : X → Y`, the unit map of the
[image](metric-spaces.images-metric-spaces.md) of `f` is short.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : short-function-Metric-Space X Y)
  where

  im-short-function-Metric-Space : Metric-Space (l1 ⊔ l3) l4
  im-short-function-Metric-Space =
    im-Metric-Space X Y (map-short-function-Metric-Space X Y f)

  map-unit-im-short-function-Metric-Space :
    type-function-Metric-Space X im-short-function-Metric-Space
  map-unit-im-short-function-Metric-Space =
    map-unit-im (map-short-function-Metric-Space X Y f)

  is-short-map-unit-im-short-function-Metric-Space :
    is-short-function-Metric-Space
      ( X)
      ( im-short-function-Metric-Space)
      ( map-unit-im-short-function-Metric-Space)
  is-short-map-unit-im-short-function-Metric-Space =
    is-short-map-short-function-Metric-Space X Y f

  short-map-unit-im-short-function-Metric-Space :
    short-function-Metric-Space X im-short-function-Metric-Space
  short-map-unit-im-short-function-Metric-Space =
    ( map-unit-im-short-function-Metric-Space ,
      is-short-map-unit-im-short-function-Metric-Space)
```

# Images of metric spaces under short maps

```agda
module metric-spaces.images-short-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.images
open import foundation.universe-levels

open import metric-spaces.images-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

Given a [short map](metric-spaces.short-maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) `f : X → Y`, the unit map of the
[image](metric-spaces.images-metric-spaces.md) of `f` is short.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : short-map-Metric-Space X Y)
  where

  im-short-map-Metric-Space : Metric-Space (l1 ⊔ l3) l4
  im-short-map-Metric-Space =
    im-Metric-Space X Y (map-short-map-Metric-Space X Y f)

  map-unit-im-short-map-Metric-Space :
    type-map-Metric-Space X im-short-map-Metric-Space
  map-unit-im-short-map-Metric-Space =
    map-unit-im (map-short-map-Metric-Space X Y f)
```

## Properties

### The unit map of the image of a short map is short

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : short-map-Metric-Space X Y)
  where

  is-short-map-unit-im-short-map-Metric-Space :
    is-short-map-Metric-Space
      ( X)
      ( im-short-map-Metric-Space X Y f)
      ( map-unit-im-short-map-Metric-Space X Y f)
  is-short-map-unit-im-short-map-Metric-Space =
    is-short-map-short-map-Metric-Space X Y f

  short-map-unit-im-short-map-Metric-Space :
    short-map-Metric-Space X (im-short-map-Metric-Space X Y f)
  short-map-unit-im-short-map-Metric-Space =
    ( map-unit-im-short-map-Metric-Space X Y f ,
      is-short-map-unit-im-short-map-Metric-Space)
```

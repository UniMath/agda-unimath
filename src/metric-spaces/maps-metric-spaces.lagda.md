# Maps between metric spaces

```agda
module metric-spaces.maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.metric-spaces
```

</details>

## Idea

{{#concept "Maps" Disambiguation="between metric spaces" Agda=type-map-Metric-Space}}
between [metric spaces](metric-spaces.metric-spaces.md) are functions between
their carrier types.

## Definitions

### The set of functions between metric spaces

```agda
module _
  {lx lx' ly ly' : Level}
  (X : Metric-Space lx lx') (Y : Metric-Space ly ly')
  where

  set-map-Metric-Space : Set (lx ⊔ ly)
  set-map-Metric-Space =
    hom-set-Set (set-Metric-Space X) (set-Metric-Space Y)

  type-map-Metric-Space : UU (lx ⊔ ly)
  type-map-Metric-Space =
    type-Metric-Space X → type-Metric-Space Y
```

### The identity map on a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  id-Metric-Space : type-map-Metric-Space M M
  id-Metric-Space = id
```

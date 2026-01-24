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

{{#concept "Maps" Disambiguation="between metric spaces" Agda=map-Metric-Space}}
between [metric spaces](metric-spaces.metric-spaces.md) are functions between
their carrier types.

## Definitions

### The set of maps between metric spaces

```agda
module _
  {lx lx' ly ly' : Level}
  (X : Metric-Space lx lx') (Y : Metric-Space ly ly')
  where

  map-set-Metric-Space : Set (lx ⊔ ly)
  map-set-Metric-Space =
    hom-set-Set (set-Metric-Space X) (set-Metric-Space Y)

  map-Metric-Space : UU (lx ⊔ ly)
  map-Metric-Space =
    type-Metric-Space X → type-Metric-Space Y
```

### The identity map on a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  id-map-Metric-Space : map-Metric-Space M M
  id-map-Metric-Space = id
```

### Constant maps between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (b : type-Metric-Space B)
  where

  const-map-Metric-Space : map-Metric-Space A B
  const-map-Metric-Space = const (type-Metric-Space A) b
```

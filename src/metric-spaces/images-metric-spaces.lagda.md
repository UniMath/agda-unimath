# Images of metric spaces

```agda
module metric-spaces.images-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.images
open import foundation.universe-levels

open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

Given a [map](metric-spaces.maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) `f : X → Y`, the
[image](foundation.images.md) of `X` under `f` is a
[subspace](metric-spaces.subspaces-metric-spaces.md) of `Y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : type-map-Metric-Space X Y)
  where

  im-Metric-Space : Metric-Space (l1 ⊔ l3) l4
  im-Metric-Space = subspace-Metric-Space Y (subtype-im f)
```

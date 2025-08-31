# Images of metric spaces under short functions

```agda
module metric-spaces.images-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.images
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.images-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
```

</details>

## Idea

Given an [isometry](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) `f : X → Y`, the unit map of the
[image](metric-spaces.images-metric-spaces.md) of `f` is an
[isometric equivalence](metric-spaces.equality-of-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : isometry-Metric-Space X Y)
  where

  im-isometry-Metric-Space : Metric-Space (l1 ⊔ l3) l4
  im-isometry-Metric-Space =
    im-Metric-Space X Y (map-isometry-Metric-Space X Y f)


```

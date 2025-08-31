# Images of metric spaces under isometries

```agda
module metric-spaces.images-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.images
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.images-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
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

  type-im-isometry-Metric-Space : UU (l1 ⊔ l3)
  type-im-isometry-Metric-Space = im (map-isometry-Metric-Space X Y f)

  equiv-unit-im-isometry-Metric-Space :
    type-Metric-Space X ≃ type-im-isometry-Metric-Space
  equiv-unit-im-isometry-Metric-Space =
    equiv-map-unit-im-emb (emb-map-isometry-Metric-Space X Y f)

  map-unit-im-isometry-Metric-Space :
    type-Metric-Space X → type-im-isometry-Metric-Space
  map-unit-im-isometry-Metric-Space =
    map-unit-im (map-isometry-Metric-Space X Y f)
```

## Properties

### The unit map of the image is an isometry

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : isometry-Metric-Space X Y)
  where

  is-isometry-map-unit-im-isometry-Metric-Space :
    is-isometry-Metric-Space
      ( X)
      ( im-isometry-Metric-Space X Y f)
      ( map-unit-im-isometry-Metric-Space X Y f)
  is-isometry-map-unit-im-isometry-Metric-Space =
    is-isometry-map-isometry-Metric-Space X Y f

  isometry-map-unit-im-isometry-Metric-Space :
    isometry-Metric-Space X (im-isometry-Metric-Space X Y f)
  isometry-map-unit-im-isometry-Metric-Space =
    ( map-unit-im-isometry-Metric-Space X Y f ,
      is-isometry-map-unit-im-isometry-Metric-Space)

  isometric-equiv-im-isometry-Metric-Space :
    isometric-equiv-Metric-Space X (im-isometry-Metric-Space X Y f)
  isometric-equiv-im-isometry-Metric-Space =
    ( equiv-unit-im-isometry-Metric-Space X Y f ,
      is-isometry-map-unit-im-isometry-Metric-Space)
```

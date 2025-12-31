# Images of metric spaces under uniformly continuous maps

```agda
module metric-spaces.images-uniformly-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.images
open import foundation.universe-levels

open import metric-spaces.images-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

Given a
[uniformly continuous map](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
between [metric spaces](metric-spaces.metric-spaces.md) `f : X → Y`, the unit
map of the [image](metric-spaces.images-metric-spaces.md) of `f` is uniformly
continuous. Any modulus of uniform continuity for `f` is a modulus of uniform
continuity for the unit map of the image.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : uniformly-continuous-map-Metric-Space X Y)
  where

  im-uniformly-continuous-map-Metric-Space : Metric-Space (l1 ⊔ l3) l4
  im-uniformly-continuous-map-Metric-Space =
    im-Metric-Space X Y (map-uniformly-continuous-map-Metric-Space X Y f)

  map-unit-im-uniformly-continuous-map-Metric-Space :
    type-map-Metric-Space X im-uniformly-continuous-map-Metric-Space
  map-unit-im-uniformly-continuous-map-Metric-Space =
    map-unit-im (map-uniformly-continuous-map-Metric-Space X Y f)
```

## Properties

### Any modulus of uniform continuity for a function is a modulus of uniform continuity for the unit map of its image

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : type-map-Metric-Space X Y)
  where

  is-modulus-of-uniform-continuity-map-unit-im-modulus-of-uniform-continuity-function-Metric-Space :
    {μ : ℚ⁺ → ℚ⁺} →
    is-modulus-of-uniform-continuity-function-Metric-Space X Y f μ →
    is-modulus-of-uniform-continuity-function-Metric-Space
      ( X)
      ( im-Metric-Space X Y f)
      ( map-unit-im f)
      ( μ)
  is-modulus-of-uniform-continuity-map-unit-im-modulus-of-uniform-continuity-function-Metric-Space
    is-modulus-μ = is-modulus-μ
```

### The unit map of a uniformly continuous function is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : uniformly-continuous-map-Metric-Space X Y)
  where

  is-uniformly-continuous-map-unit-im-uniformly-continuous-map-Metric-Space :
    is-uniformly-continuous-map-Metric-Space
      ( X)
      ( im-uniformly-continuous-map-Metric-Space X Y f)
      ( map-unit-im-uniformly-continuous-map-Metric-Space X Y f)
  is-uniformly-continuous-map-unit-im-uniformly-continuous-map-Metric-Space =
    is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space X Y f

  uniformly-continuous-map-unit-im-uniformly-continuous-map-Metric-Space :
    uniformly-continuous-map-Metric-Space
      ( X)
      ( im-uniformly-continuous-map-Metric-Space X Y f)
  uniformly-continuous-map-unit-im-uniformly-continuous-map-Metric-Space =
    ( map-unit-im-uniformly-continuous-map-Metric-Space X Y f ,
      is-uniformly-continuous-map-unit-im-uniformly-continuous-map-Metric-Space)
```

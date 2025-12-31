# The metric space of short functions between metric spaces

```agda
module metric-spaces.metric-space-of-short-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.metric-space-of-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

[Short functions](metric-spaces.short-maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) inherit the
[metric subspace](metric-spaces.subspaces-metric-spaces.md) structure of the
[function metric space](metric-spaces.metric-space-of-maps-metric-spaces.md).
This defines the
{{#concept "metric space of short functions between metric spaces" Agda=metric-space-of-short-maps-Metric-Space}}.

## Definitions

### The metric space of short functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-of-short-maps-Metric-Space :
    Metric-Space (l1 ⊔ l2 ⊔ l1' ⊔ l2') (l1 ⊔ l2')
  metric-space-of-short-maps-Metric-Space =
    subspace-Metric-Space
      ( metric-space-of-maps-Metric-Space A B)
      ( is-short-map-prop-Metric-Space A B)
```

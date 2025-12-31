# The metric space of isometries between metric spaces

```agda
module metric-spaces.metric-space-of-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

[Isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) inherit the
[metric subspace](metric-spaces.subspaces-metric-spaces.md) structure of the
[function metric space](metric-spaces.metric-space-of-maps-metric-spaces.md).
This defines the
{{#concept "metric space of isometries between metric spaces" Agda=metric-space-of-isometries-Metric-Space}}.

## Definitions

### The metric space of isometries between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-of-isometries-Metric-Space :
    Metric-Space (l1 ⊔ l2 ⊔ l1' ⊔ l2') (l1 ⊔ l2')
  metric-space-of-isometries-Metric-Space =
    subspace-Metric-Space
      ( metric-space-of-functions-Metric-Space A B)
      ( is-isometry-prop-Metric-Space A B)
```

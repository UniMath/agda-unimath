# The metric space of Lipschitz maps between metric spaces

```agda
module metric-spaces.metric-space-of-lipschitz-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.metric-space-of-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

[Lipschitz maps](metric-spaces.lipschitz-maps-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) inherit the
[metric subspace](metric-spaces.subspaces-metric-spaces.md) structure of the
[map metric space](metric-spaces.metric-space-of-maps-metric-spaces.md). This
defines the
{{#concept "metric space of Lipschitz maps between metric spaces" Agda=metric-space-of-lipschitz-maps-Metric-Space}}.

## Definitions

### The metric space of Lipschitz maps between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-of-lipschitz-maps-Metric-Space :
    Metric-Space (l1 ⊔ l2 ⊔ l1' ⊔ l2') (l1 ⊔ l2')
  metric-space-of-lipschitz-maps-Metric-Space =
    subspace-Metric-Space
      ( metric-space-of-functions-Metric-Space A B)
      ( is-lipschitz-prop-map-Metric-Space A B)
```

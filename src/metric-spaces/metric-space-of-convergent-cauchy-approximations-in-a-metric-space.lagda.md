# The metric space of convergent cauchy approximations in a metric space

```agda
module metric-spaces.metric-space-of-convergent-cauchy-approximations-in-a-metric-space where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The type of
[convergent Cauchy approximations](metric-spaces.convergent-cauchy-approximations-metric-spaces.md)
in a [metric space](metric-spaces.metric-spaces.md) inherits the
[metric substructure](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of Cauchy approximations](metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space.md).
This is the
{{#concept "metric space of convergent Cauchy approximations" Disambiguation="in a metric space" Agda=metric-space-convergent-cauchy-approximations-Metric-Space}}
in a metric space.

## Definitions

### The metric space of cauchy approximations in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  metric-space-convergent-cauchy-approximations-Metric-Space :
    Metric-Space (l1 ⊔ l2) l2
  metric-space-convergent-cauchy-approximations-Metric-Space =
    subspace-Metric-Space
      ( metric-space-cauchy-approximations-Metric-Space A)
      ( is-convergent-prop-cauchy-approximation-Metric-Space A)
```

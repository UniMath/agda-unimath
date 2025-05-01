# The metric space of functions between metric spaces

```agda
module metric-spaces.metric-space-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.premetric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

[Functions](metric-spaces.functions-metric-spaces.md) between metric spaces
inherit the
[product metric structure](metric-spaces.dependent-products-metric-spaces.md) of
their codomain. This is the
{{#concept "metric space of functions between metric spaces" Agda=metric-space-function-Metric-Space}};
[short functions](metric-spaces.short-functions-metric-spaces.md) and
[isometries](metric-spaces.isometries-metric-spaces.md) inherit the
[metric subspace](metric-spaces.subspaces-metric-spaces.md) structure.

## Definitions

### The metric space of functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-function-Metric-Space : Metric-Space (l1 ⊔ l1') (l1 ⊔ l2')
  metric-space-function-Metric-Space =
    Π-Metric-Space (type-Metric-Space A) (λ _ → B)
```

### The metric space of short functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-short-function-Metric-Space :
    Metric-Space (l1 ⊔ l2 ⊔ l1' ⊔ l2') (l1 ⊔ l2')
  metric-space-short-function-Metric-Space =
    subspace-Metric-Space
      ( metric-space-function-Metric-Space A B)
      ( is-short-function-prop-Metric-Space A B)
```

### The metric space of isometries between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-isometry-Metric-Space :
    Metric-Space (l1 ⊔ l2 ⊔ l1' ⊔ l2') (l1 ⊔ l2')
  metric-space-isometry-Metric-Space =
    subspace-Metric-Space
      ( metric-space-function-Metric-Space A B)
      ( is-isometry-prop-Metric-Space A B)
```

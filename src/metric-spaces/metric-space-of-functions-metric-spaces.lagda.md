# The metric space of functions between metric spaces

```agda
module metric-spaces.metric-space-of-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

[Functions](metric-spaces.functions-metric-spaces.md) between metric spaces
inherit the
[product metric structure](metric-spaces.dependent-products-metric-spaces.md) of
their codomain. This defines
{{#concept "metric space of functions between metric spaces" Agda=metric-space-function-Metric-Space}}.

## Definitions

### The metric space of functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  metric-space-of-functions-Metric-Space : Metric-Space (l1 ⊔ l1') (l1 ⊔ l2')
  metric-space-of-functions-Metric-Space =
    Π-Metric-Space (type-Metric-Space A) (λ _ → B)
```

# Functions between metric spaces

```agda
module metric-spaces.functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.metric-spaces
```

</details>

## Idea

{{#concept "Functions" Disambiguation="between metric spaces" Agda=function-carrier-type-Metric-Space}}
between metric spaces are (not necessarily continuous) functions between their
carrier types.

## Definitions

### Functions between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  function-carrier-type-Metric-Space : UU (l1 ⊔ l2)
  function-carrier-type-Metric-Space = type-Metric-Space A → type-Metric-Space B
```

### The identity function on a metric space

```agda
module _
  {l : Level} (M : Metric-Space l)
  where

  id-Metric-Space : function-carrier-type-Metric-Space M M
  id-Metric-Space x = x
```

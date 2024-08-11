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

Functions between metric spaces are functions between their carrier types

## Definitions

### Functions between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  fun-Metric-Space : UU (l1 ⊔ l2)
  fun-Metric-Space = type-Metric-Space A → type-Metric-Space B
```

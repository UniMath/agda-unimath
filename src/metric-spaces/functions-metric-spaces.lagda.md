# Functions between metric spaces

```agda
module metric-spaces.functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.sets
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

## Properties

### The type of functions between metric spaces is a set

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  is-set-function-carrier-type-Metric-Space :
    is-set (function-carrier-type-Metric-Space A B)
  is-set-function-carrier-type-Metric-Space =
    is-set-Π (λ x → is-set-type-Metric-Space B)

  set-function-carrier-type-Metric-Space : Set (l1 ⊔ l2)
  set-function-carrier-type-Metric-Space =
    function-carrier-type-Metric-Space A B ,
    is-set-function-carrier-type-Metric-Space
```

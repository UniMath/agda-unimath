# Functions between metric spaces

```agda
module metric-spaces.functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.premetric-spaces
```

</details>

## Idea

{{#concept "Functions" Disambiguation="between metric spaces" Agda=function-carrier-type-Metric-Space}}
between [metric spaces](metric-spaces.metric-spaces.md) are functions between
their carrier types.

## Definitions

### Functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  function-carrier-type-Metric-Space : UU (l1 ⊔ l1')
  function-carrier-type-Metric-Space =
    function-carrier-type-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
```

### The identity function on a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  id-Metric-Space : function-carrier-type-Metric-Space M M
  id-Metric-Space = id
```

## Properties

### The type of functions between metric spaces is a set

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  is-set-function-carrier-type-Metric-Space :
    is-set (function-carrier-type-Metric-Space A B)
  is-set-function-carrier-type-Metric-Space =
    is-set-Π (λ x → is-set-type-Metric-Space B)

  set-function-carrier-type-Metric-Space : Set (l1 ⊔ l1')
  set-function-carrier-type-Metric-Space =
    function-carrier-type-Metric-Space A B ,
    is-set-function-carrier-type-Metric-Space
```

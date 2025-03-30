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

{{#concept "Functions" Disambiguation="between metric spaces" Agda=map-type-Metric-Space}}
between [metric spaces](metric-spaces.metric-spaces.md) are functions between
their carrier types.

## Definitions

### Functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  map-type-Metric-Space : UU (l1 ⊔ l1')
  map-type-Metric-Space =
    map-type-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
```

### Binary functions between metric spaces

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4) (C : Metric-Space l5 l6)
  where

  binary-map-type-Metric-Space : UU (l1 ⊔ l3 ⊔ l5)
  binary-map-type-Metric-Space =
    binary-map-type-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( premetric-Metric-Space C)
```

### The identity function on a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  id-Metric-Space : map-type-Metric-Space M M
  id-Metric-Space = id
```

## Properties

### The type of functions between metric spaces is a set

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  is-set-map-type-Metric-Space :
    is-set (map-type-Metric-Space A B)
  is-set-map-type-Metric-Space =
    is-set-Π (λ x → is-set-type-Metric-Space B)

  set-map-type-Metric-Space : Set (l1 ⊔ l1')
  set-map-type-Metric-Space =
    map-type-Metric-Space A B ,
    is-set-map-type-Metric-Space
```

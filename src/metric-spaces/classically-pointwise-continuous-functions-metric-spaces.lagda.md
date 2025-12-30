# Classically pointwise continuous functions in metric spaces

```agda
module metric-spaces.classically-pointwise-continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-countable-choice
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.classical-limits-of-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pointwise-continuous-functions-metric-spaces
```

</details>

## Idea

A
{{#concept "classically pointwise continuous function" Disambiguation="between metric spaces" Agda=pointwise-continuous-map-Metric-Space}}
from a [metric space](metric-spaces.metric-spaces.md) `X` to a metric space `Y`
is a function `f : X → Y` such that for every `x : X`, the
[classical limit](metric-spaces.classical-limits-of-functions-metric-spaces.md)
of `f` as it approaches `x` is `f x`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  is-classically-pointwise-continuous-prop-map-Metric-Space :
    Prop (l1 ⊔ l2 ⊔ l4)
  is-classically-pointwise-continuous-prop-map-Metric-Space =
    Π-Prop
      ( type-Metric-Space X)
      ( λ x → is-classical-limit-prop-map-Metric-Space X Y f x (f x))

  is-classically-pointwise-continuous-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-classically-pointwise-continuous-map-Metric-Space =
    type-Prop is-classically-pointwise-continuous-prop-map-Metric-Space
```

## Properties

### Constructively pointwise continuous functions are classically pointwise continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : pointwise-continuous-map-Metric-Space X Y)
  where

  abstract
    is-classically-pointwise-continuous-pointwise-continuous-map-Metric-Space :
      is-classically-pointwise-continuous-map-Metric-Space
        ( X)
        ( Y)
        ( map-pointwise-continuous-map-Metric-Space X Y f)
    is-classically-pointwise-continuous-pointwise-continuous-map-Metric-Space
      x =
      is-classical-limit-is-limit-map-Metric-Space
        ( X)
        ( Y)
        ( map-pointwise-continuous-map-Metric-Space X Y f)
        ( x)
        ( map-pointwise-continuous-map-Metric-Space X Y f x)
        ( is-pointwise-continuous-map-pointwise-continuous-map-Metric-Space
          ( X)
          ( Y)
          ( f)
          ( x))
```

### Assuming countable choice, classically pointwise continuous functions are continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (acω : ACω)
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  abstract
    is-pointwise-continuous-map-is-classically-pointwise-continuous-map-acω-Metric-Space :
      is-classically-pointwise-continuous-map-Metric-Space X Y f →
      is-pointwise-continuous-map-Metric-Space X Y f
    is-pointwise-continuous-is-classically-pointwise-continuous-map-acω-Metric-Space
      H x =
      is-limit-is-classical-limit-map-acω-Metric-Space
        ( acω)
        ( X)
        ( Y)
        ( f)
        ( x)
        ( f x)
        ( H x)
```

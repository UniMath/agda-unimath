# Pointwise ε-δ continuous maps between metric spaces

```agda
module metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-countable-choice
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.epsilon-delta-limits-of-maps-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pointwise-continuous-maps-metric-spaces
```

</details>

## Idea

An
{{#concept "pointwise ε-δ continuous map" Disambiguation="between metric spaces" Agda=pointwise-continuous-map-Metric-Space}}
from a [metric space](metric-spaces.metric-spaces.md) `X` to a metric space `Y`
is a map `f : X → Y` such that for every `x : X`, the
[ε-δ limit](metric-spaces.epsilon-delta-limits-of-maps-metric-spaces.md) of `f`
as it approaches `x` is `f x`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  where

  is-pointwise-ε-δ-continuous-prop-map-Metric-Space :
    Prop (l1 ⊔ l2 ⊔ l4)
  is-pointwise-ε-δ-continuous-prop-map-Metric-Space =
    Π-Prop
      ( type-Metric-Space X)
      ( λ x → is-ε-δ-limit-prop-map-Metric-Space X Y f x (f x))

  is-pointwise-ε-δ-continuous-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-pointwise-ε-δ-continuous-map-Metric-Space =
    type-Prop is-pointwise-ε-δ-continuous-prop-map-Metric-Space
```

## Properties

### Pointwise continuous maps are pointwise ε-δ continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : pointwise-continuous-map-Metric-Space X Y)
  where

  abstract
    is-pointwise-ε-δ-continuous-map-pointwise-continuous-map-Metric-Space :
      is-pointwise-ε-δ-continuous-map-Metric-Space
        ( X)
        ( Y)
        ( map-pointwise-continuous-map-Metric-Space X Y f)
    is-pointwise-ε-δ-continuous-map-pointwise-continuous-map-Metric-Space
      x =
      is-ε-δ-limit-is-limit-map-Metric-Space
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

### Assuming countable choice, pointwise ε-δ continuous maps are pointwise continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (acω : level-ACℕ (l1 ⊔ l2 ⊔ l4))
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  where

  abstract
    is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-ACℕ-Metric-Space :
      is-pointwise-ε-δ-continuous-map-Metric-Space X Y f →
      is-pointwise-continuous-map-Metric-Space X Y f
    is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-ACℕ-Metric-Space
      H x =
      is-limit-is-ε-δ-limit-map-ACℕ-Metric-Space
        ( acω)
        ( X)
        ( Y)
        ( f)
        ( x)
        ( f x)
        ( H x)
```

## See also

- [Pointwise continuous maps between metric spaces](metric-spaces.pointwise-continuous-maps-metric-spaces.md)

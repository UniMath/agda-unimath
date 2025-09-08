# Totally bounded subspaces of metric spaces

```agda
module metric-spaces.totally-bounded-subspaces-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.images-subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A
{{#concept "totally bounded" disambiguation="subspace of a metric space" WDID=Q1362228 WD="totally bounded space" Agda=is-totally-bounded-subset-Metric-Space}}
subspace of a [metric space](metric-spaces.metric-spaces.md) is a
[subspace](metric-spaces.subspaces-metric-spaces.md) that is
[totally bounded](metric-spaces.totally-bounded-metric-spaces.md).

## Definition

```agda
totally-bounded-subspace-Metric-Space :
  {l1 l2 : Level} (l3 l4 : Level) → Metric-Space l1 l2 →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
totally-bounded-subspace-Metric-Space l3 l4 X =
  Σ ( subset-Metric-Space l3 X)
    ( λ S → is-totally-bounded-Metric-Space l4 (subspace-Metric-Space X S))

module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2)
  (S : totally-bounded-subspace-Metric-Space l3 l4 X)
  where

  subset-totally-bounded-subspace-Metric-Space : subset-Metric-Space l3 X
  subset-totally-bounded-subspace-Metric-Space = pr1 S

  subspace-totally-bounded-subspace-Metric-Space : Metric-Space (l1 ⊔ l3) l2
  subspace-totally-bounded-subspace-Metric-Space =
    subspace-Metric-Space X subset-totally-bounded-subspace-Metric-Space

  is-totally-bounded-subspace-totally-bounded-subspace-Metric-Space :
    is-totally-bounded-Metric-Space
      ( l4)
      ( subspace-totally-bounded-subspace-Metric-Space)
  is-totally-bounded-subspace-totally-bounded-subspace-Metric-Space =
    pr2 S
```

## Properties

### The image of a totally bounded subspace under a uniformly continuous function

```agda
im-uniformly-continuous-function-totally-bounded-subspace-Metric-Space :
  {l1 l2 l3 l4 l5 l6 : Level} →
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) →
  (f : uniformly-continuous-function-Metric-Space X Y) →
  totally-bounded-subspace-Metric-Space l5 l6 X →
  totally-bounded-subspace-Metric-Space (l1 ⊔ l3 ⊔ l5) (l1 ⊔ l3 ⊔ l5 ⊔ l6) Y
im-uniformly-continuous-function-totally-bounded-subspace-Metric-Space
  X Y f (S , tbS) =
    ( im-subtype (map-uniformly-continuous-function-Metric-Space X Y f) S ,
      is-totally-bounded-im-uniformly-continuous-function-is-totally-bounded-Metric-Space
        ( subspace-Metric-Space X S)
        ( Y)
        ( tbS)
        ( comp-uniformly-continuous-function-Metric-Space
          ( subspace-Metric-Space X S)
          ( X)
          ( Y)
          ( f)
          ( uniformly-continuous-inclusion-subspace-Metric-Space X S)))
```

# Extensions of metric spaces

```agda
module metric-spaces.extensions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

An
{{#concept "extension" Disambiguation="of a metric space" Agda=extension-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `P`is a metric space `Q`
together with an [isometry](metric-spaces.isometries-metric-spaces.md)
`i : P → Q`.

## Definition

### Extensions of metric spaces

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (P : Metric-Space l1 l2)
  where

  extension-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  extension-Metric-Space =
    Σ ( Metric-Space l3 l4)
      ( isometry-Metric-Space P)

module _
  {l1 l2 l3 l4 : Level}
  (P : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 P)
  where

  metric-space-extension-Metric-Space : Metric-Space l3 l4
  metric-space-extension-Metric-Space = pr1 E

  pseudometric-space-extension-Metric-Space : Pseudometric-Space l3 l4
  pseudometric-space-extension-Metric-Space =
    pseudometric-Metric-Space metric-space-extension-Metric-Space

  type-metric-space-extension-Metric-Space : UU l3
  type-metric-space-extension-Metric-Space =
    type-Metric-Space metric-space-extension-Metric-Space

  isometry-metric-space-extension-Metric-Space :
    isometry-Metric-Space
      ( P)
      ( metric-space-extension-Metric-Space)
  isometry-metric-space-extension-Metric-Space = pr2 E

  map-metric-space-extension-Metric-Space :
    type-Metric-Space P →
    type-Metric-Space metric-space-extension-Metric-Space
  map-metric-space-extension-Metric-Space =
    map-isometry-Metric-Space
      ( P)
      ( metric-space-extension-Metric-Space)
      ( isometry-metric-space-extension-Metric-Space)

  is-isometry-map-metric-space-extension-Metric-Space :
    is-isometry-Metric-Space
      ( P)
      ( metric-space-extension-Metric-Space)
      ( map-metric-space-extension-Metric-Space)
  is-isometry-map-metric-space-extension-Metric-Space =
    is-isometry-map-isometry-Metric-Space
      ( P)
      ( metric-space-extension-Metric-Space)
      ( isometry-metric-space-extension-Metric-Space)
```

## Properties

### The identity extension

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  where

  id-extension-Metric-Space : extension-Metric-Space l1 l2 M
  id-extension-Metric-Space =
    (M , id-isometry-Metric-Space M)
```

### Composition of extensions of metric spaces

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  ( M : Metric-Space l1 l2)
  ( E : extension-Metric-Space l3 l4 M)
  ( F : extension-Metric-Space l5 l6
    ( metric-space-extension-Metric-Space M E))
  where

  comp-extension-Metric-Space : extension-Metric-Space l5 l6 M
  pr1 comp-extension-Metric-Space =
    metric-space-extension-Metric-Space
      ( metric-space-extension-Metric-Space M E)
      ( F)
  pr2 comp-extension-Metric-Space =
    comp-isometry-Metric-Space
      ( M)
      ( metric-space-extension-Metric-Space M E)
      ( metric-space-extension-Metric-Space
        ( metric-space-extension-Metric-Space M E)
        ( F))
      ( isometry-metric-space-extension-Metric-Space
        ( metric-space-extension-Metric-Space M E)
        ( F))
      ( isometry-metric-space-extension-Metric-Space M E)
```

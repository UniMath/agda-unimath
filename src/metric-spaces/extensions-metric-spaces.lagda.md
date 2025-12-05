# Extensions of metric spaces

```agda
module metric-spaces.extensions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

An
{{#concept "extension" Disambiguation="of a metric space" Agda=extension-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `P`is a
metric space `Q` together with an
[isometry](metric-spaces.isometries-metric-spaces.md) `i : P → Q`.

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

  isometry-metric-space-extension-Metric-Space :
    isometry-Metric-Space
      ( P)
      ( metric-space-extension-Metric-Space)
  isometry-metric-space-extension-Metric-Space = pr2 E

  map-isometry-metric-space-extension-Metric-Space :
    type-Metric-Space P →
    type-Metric-Space metric-space-extension-Metric-Space
  map-isometry-metric-space-extension-Metric-Space =
    map-isometry-Metric-Space
      ( P)
      ( metric-space-extension-Metric-Space)
      ( isometry-metric-space-extension-Metric-Space)

  is-isometry-map-extension-Metric-Space :
    is-isometry-Metric-Space
      ( P)
      ( metric-space-extension-Metric-Space)
      ( map-isometry-metric-space-extension-Metric-Space)
  is-isometry-map-extension-Metric-Space =
    is-isometry-map-isometry-Metric-Space
      ( P)
      ( metric-space-extension-Metric-Space)
      ( isometry-metric-space-extension-Metric-Space)
```

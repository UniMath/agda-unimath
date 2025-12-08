# Action on Cauchy approximations of extensions of metric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

A [extension of a metric space](metric-spaces.extensions-metric-spaces.md)
induces an isometry between the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletion-of-metric-spaces.md),
hence, an
[extension of pseudometric spaces](metric-spaces.extensions-pseudometric-spaces.md)
of the Cauchy precompletion.

## Definition

### Action of extensions of metric spaces on Cauchy approximations

```agda
module _
  {l1 l2 l3 l4 : Level} (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where

  isometry-cauchy-pseudocompletion-extension-Metric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M E))
  isometry-cauchy-pseudocompletion-extension-Metric-Space =
    isometry-map-cauchy-approximation-isometry-Pseudometric-Space
      ( pseudometric-Metric-Space M)
      ( pseudometric-space-extension-Metric-Space M E)
      ( isometry-metric-space-extension-Metric-Space M E)

  map-cauchy-approximation-extension-Metric-Space :
    cauchy-approximation-Metric-Space M →
    cauchy-approximation-Metric-Space
      ( metric-space-extension-Metric-Space M E)
  map-cauchy-approximation-extension-Metric-Space =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M E))
      ( isometry-cauchy-pseudocompletion-extension-Metric-Space)

  is-isometry-map-cauchy-approximation-extension-Metric-Space :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M E))
      ( map-cauchy-approximation-extension-Metric-Space)
  is-isometry-map-cauchy-approximation-extension-Metric-Space =
    is-isometry-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space M)
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-extension-Metric-Space M E))
      ( isometry-cauchy-pseudocompletion-extension-Metric-Space)
```

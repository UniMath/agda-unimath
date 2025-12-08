# Cauchy-dense extensions of metric spaces

```agda
module metric-spaces.cauchy-dense-extensions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
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
open import metric-spaces.limit-points-extensions-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

An [extension of a metric space](metric-spaces.extensions-metric-spaces.md]
`i : M → N` is called
{{#concept "Cauchy-dense" Disambiguation="extension of metric space" Agda=is-cauchy-dense-prop-extension-Metric-Space}}
if all points in `N` are
[limit points](metrics-spaces.limit-points-extensions-metric-spaces.md) of the
extension, i.e. limit of the
[image](metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces)
of some
[Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md) in
`M`.

## Definition

### The property of being a Cauchy-dense extension of metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where

  is-cauchy-dense-prop-extension-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-dense-prop-extension-Metric-Space =
    Π-Prop
      ( type-metric-space-extension-Metric-Space M E)
      ( is-limit-prop-point-extension-Metric-Space M E)
```

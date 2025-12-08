# Complete extensions of metric spaces

```agda
module metric-spaces.complete-extensions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces
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
open import metric-spaces.precomplete-extensions-metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

An [extension of a metric space](metric-spaces.extensions-metric-spaces.md]
`i : M → N` is called
{{#concept "complete" Disambiguation="extension of metric space" Agda=is-complete-prop-extension-Metric-Space}}
if `N` is [complete](metric-spaces.complete-metric-spaces.md).

Any **complete** extension of metric space is
[precomplete](metric-spaces.precomplete-extensions-metric-spaces.md).

## Definition

### The property of being a complete metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where

  is-complete-prop-extension-Metric-Space : Prop (l3 ⊔ l4)
  is-complete-prop-extension-Metric-Space =
    is-complete-prop-Metric-Space
      (metric-space-extension-Metric-Space M E)

  is-complete-extension-Metric-Space : UU (l3 ⊔ l4)
  is-complete-extension-Metric-Space =
    type-Prop is-complete-prop-extension-Metric-Space

  is-prop-is-complete-extension-Metric-Space :
    is-prop is-complete-extension-Metric-Space
  is-prop-is-complete-extension-Metric-Space =
    is-prop-type-Prop is-complete-prop-extension-Metric-Space
```

## Properties

### Any complete extension is precomplete

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where

  is-precomplete-is-complete-extension-Metric-Space :
    is-complete-extension-Metric-Space M E →
    is-precomplete-extension-Metric-Space M E
  is-precomplete-is-complete-extension-Metric-Space H =
    H ∘ map-cauchy-approximation-extension-Metric-Space M E
```

# Precompelte extensions of metric spaces

```agda
module metric-spaces.precomplete-extensions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
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
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

An [extension of a metric space](metric-spaces.extensions-metric-spaces.md]
`i : M → N` is called
{{#concept "precomplete" Disambiguation="extension of metric space" Agda=is-precomplete-prop-extension-Metric-Space}}
if the
[images](metric-spaces.action-on-cauchy-approximations-extensions-metric-spaces.md)
of all
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
`M` are
[convergent](metric-spaces.convergent-cauchy-approximations-metric-spaces.md) in
`N`.

## Definition

### The property of being a precomplete extension of metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Metric-Space l1 l2)
  (E : extension-Metric-Space l3 l4 M)
  where

  is-precomplete-prop-extension-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-precomplete-prop-extension-Metric-Space =
    Π-Prop
      ( cauchy-approximation-Metric-Space M)
      ( λ u →
        is-convergent-prop-cauchy-approximation-Metric-Space
          ( metric-space-extension-Metric-Space M E)
          ( map-cauchy-approximation-extension-Metric-Space M E u))

  is-precomplete-extension-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-precomplete-extension-Metric-Space =
    type-Prop is-precomplete-prop-extension-Metric-Space

  is-prop-is-precomplete-extension-Metric-Space :
    is-prop is-precomplete-extension-Metric-Space
  is-prop-is-precomplete-extension-Metric-Space =
    is-prop-type-Prop is-precomplete-prop-extension-Metric-Space
```

# Cauchy approximations in metric spaces

```agda
module metric-spaces.cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-premetric-spaces
open import metric-spaces.limits-of-cauchy-approximations-in-premetric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy approximation" Disambiguation="in a metric space" Agda=is-cauchy-approximation-Metric-Space}}
in a [metric space](metric-spaces.metric-spaces.md) is a
[Cauchy approximation](metric-spaces.cauchy-approximations-premetric-spaces.md)
in the carrier [premetric space](metric-spaces.premetric-spaces.md).

## Definitions

### Cauchy approximations in metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-cauchy-approximation-prop-Metric-Space :
    (ℚ⁺ → type-Metric-Space A) → Prop l2
  is-cauchy-approximation-prop-Metric-Space =
    is-cauchy-approximation-prop-Premetric-Space
      ( premetric-Metric-Space A)

  is-cauchy-approximation-Metric-Space :
    (ℚ⁺ → type-Metric-Space A) → UU l2
  is-cauchy-approximation-Metric-Space =
    type-Prop ∘ is-cauchy-approximation-prop-Metric-Space

  cauchy-approximation-Metric-Space : UU (l1 ⊔ l2)
  cauchy-approximation-Metric-Space =
    type-subtype is-cauchy-approximation-prop-Metric-Space
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  where

  map-cauchy-approximation-Metric-Space :
    ℚ⁺ → type-Metric-Space A
  map-cauchy-approximation-Metric-Space = pr1 f

  is-cauchy-approximation-map-cauchy-approximation-Metric-Space :
    (ε δ : ℚ⁺) →
    neighborhood-Metric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Metric-Space ε)
      ( map-cauchy-approximation-Metric-Space δ)
  is-cauchy-approximation-map-cauchy-approximation-Metric-Space = pr2 f
```

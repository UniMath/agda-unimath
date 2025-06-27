# Convergent Cauchy approximations in metric spaces (WIP)

```agda
module metric-spaces.convergent-cauchy-approximations-metric-spaces-WIP where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces-WIP
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces-WIP
open import metric-spaces.metric-spaces-WIP
```

</details>

## Idea

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
in a [metric space](metric-spaces.metric-spaces.md) is
{{#concept "convergent" Disambiguation="Cauchy approximation in a metric space" agda=is-convergent-cauchy-approximation-Metric-Space-WIP}}
if it has a
[limit](metric-spaces.limits-of-cauchy-approximations-metric-spaces-WIP.md).
Because limits of Cauchy approximations in metric spaces are unique, this is a
[subtype](foundation.subtypes.md) of the type of Cauchy approximations.

## Definitions

### The property of being a convergent Cauchy approximation in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  (f : cauchy-approximation-Metric-Space-WIP A)
  where

  is-convergent-cauchy-approximation-Metric-Space-WIP : UU (l1 ⊔ l2)
  is-convergent-cauchy-approximation-Metric-Space-WIP =
    Σ ( type-Metric-Space-WIP A)
      ( is-limit-cauchy-approximation-Metric-Space-WIP A f)

  limit-is-convergent-cauchy-approximation-Metric-Space-WIP :
    is-convergent-cauchy-approximation-Metric-Space-WIP →
    type-Metric-Space-WIP A
  limit-is-convergent-cauchy-approximation-Metric-Space-WIP = pr1

  is-limit-limit-is-convergent-cauchy-approximation-Metric-Space-WIP :
    (x : is-convergent-cauchy-approximation-Metric-Space-WIP) →
    is-limit-cauchy-approximation-Metric-Space-WIP
      ( A)
      ( f)
      ( limit-is-convergent-cauchy-approximation-Metric-Space-WIP x)
  is-limit-limit-is-convergent-cauchy-approximation-Metric-Space-WIP = pr2

  abstract
    is-prop-is-convergent-cauchy-approximation-Metric-Space-WIP :
      is-prop is-convergent-cauchy-approximation-Metric-Space-WIP
    is-prop-is-convergent-cauchy-approximation-Metric-Space-WIP =
      is-prop-all-elements-equal
        ( λ x y →
          eq-type-subtype
            ( is-limit-cauchy-approximation-prop-Metric-Space-WIP A f)
            ( all-eq-is-limit-cauchy-approximation-Metric-Space-WIP
              ( A)
              ( f)
              ( limit-is-convergent-cauchy-approximation-Metric-Space-WIP x)
              ( limit-is-convergent-cauchy-approximation-Metric-Space-WIP y)
              ( is-limit-limit-is-convergent-cauchy-approximation-Metric-Space-WIP
                x)
              ( is-limit-limit-is-convergent-cauchy-approximation-Metric-Space-WIP
                y)))

  is-convergent-prop-cauchy-approximation-Metric-Space-WIP : Prop (l1 ⊔ l2)
  is-convergent-prop-cauchy-approximation-Metric-Space-WIP =
    is-convergent-cauchy-approximation-Metric-Space-WIP ,
    is-prop-is-convergent-cauchy-approximation-Metric-Space-WIP
```

### The type of convergent Cauchy approximations in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  convergent-cauchy-approximation-Metric-Space-WIP : UU (l1 ⊔ l2)
  convergent-cauchy-approximation-Metric-Space-WIP =
    type-subtype (is-convergent-prop-cauchy-approximation-Metric-Space-WIP A)
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  (f : convergent-cauchy-approximation-Metric-Space-WIP A)
  where

  approximation-convergent-cauchy-approximation-Metric-Space-WIP :
    cauchy-approximation-Metric-Space-WIP A
  approximation-convergent-cauchy-approximation-Metric-Space-WIP = pr1 f

  map-convergent-cauchy-approximation-Metric-Space-WIP :
    ℚ⁺ → type-Metric-Space-WIP A
  map-convergent-cauchy-approximation-Metric-Space-WIP =
    map-cauchy-approximation-Metric-Space-WIP
      A
      approximation-convergent-cauchy-approximation-Metric-Space-WIP

  is-cauchy-approximation-map-convergent-cauchy-approximation-Metric-Space-WIP :
    (ε δ : ℚ⁺) →
    neighborhood-Metric-Space-WIP
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-convergent-cauchy-approximation-Metric-Space-WIP ε)
      ( map-convergent-cauchy-approximation-Metric-Space-WIP δ)
  is-cauchy-approximation-map-convergent-cauchy-approximation-Metric-Space-WIP =
    is-cauchy-approximation-map-cauchy-approximation-Metric-Space-WIP
      A
      approximation-convergent-cauchy-approximation-Metric-Space-WIP

  limit-convergent-cauchy-approximation-Metric-Space-WIP :
    type-Metric-Space-WIP A
  limit-convergent-cauchy-approximation-Metric-Space-WIP = pr1 (pr2 f)

  is-limit-limit-convergent-cauchy-approximation-Metric-Space-WIP :
    (ε δ : ℚ⁺) →
    neighborhood-Metric-Space-WIP
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-convergent-cauchy-approximation-Metric-Space-WIP ε)
      ( limit-convergent-cauchy-approximation-Metric-Space-WIP)
  is-limit-limit-convergent-cauchy-approximation-Metric-Space-WIP = pr2 (pr2 f)
```

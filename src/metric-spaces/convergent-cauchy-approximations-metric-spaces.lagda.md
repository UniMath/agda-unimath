# Convergent Cauchy approximations in metric spaces

```agda
module metric-spaces.convergent-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-in-premetric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
in a [metric space](metric-spaces.metric-spaces.md) is
{{#concept "convergent" Disambiguation="Cauchy approximation in a megtric space" agda=is-convergent-cauchy-approximation-Metric-Space}}
if it has a
[limit](metric-spaces.limits-of-cauchy-approximations-in-premetric-spaces.md).

Because limits of cauchy approximations in metric spaces are unique, this is a
[subtype](foundation.subtypes.md) of the type of Cauchy approximations.

## Definitions

### The property of being a convergent Cauchy approximation in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  where

  is-convergent-cauchy-approximation-Metric-Space : UU (l1 ⊔ l2)
  is-convergent-cauchy-approximation-Metric-Space =
    Σ (type-Metric-Space A) (is-limit-cauchy-approximation-Metric-Space A f)

  is-prop-is-convergent-cauchy-approximation-Metric-Space :
    is-prop is-convergent-cauchy-approximation-Metric-Space
  is-prop-is-convergent-cauchy-approximation-Metric-Space =
    is-prop-all-elements-equal
      ( λ x y →
        eq-type-subtype
          ( is-limit-cauchy-approximation-prop-Premetric-Space
            ( premetric-Metric-Space A)
            ( f))
          ( all-eq-limit-cauchy-approximation-Metric-Space A f (pr2 x) (pr2 y)))

  is-convergent-cauchy-approximation-prop-Metric-Space : Prop (l1 ⊔ l2)
  is-convergent-cauchy-approximation-prop-Metric-Space =
    is-convergent-cauchy-approximation-Metric-Space ,
    is-prop-is-convergent-cauchy-approximation-Metric-Space
```

### The type of convergent cauchy approximations in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  Convergent-cauchy-approximation-Metric-Space : UU (l1 ⊔ l2)
  Convergent-cauchy-approximation-Metric-Space =
    type-subtype (is-convergent-cauchy-approximation-prop-Metric-Space A)
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : Convergent-cauchy-approximation-Metric-Space A)
  where

  approximation-Convergent-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space A
  approximation-Convergent-cauchy-approximation-Metric-Space = pr1 f

  map-Convergent-cauchy-approximation-Metric-Space : ℚ⁺ → type-Metric-Space A
  map-Convergent-cauchy-approximation-Metric-Space =
    map-cauchy-approximation-Metric-Space
      A
      approximation-Convergent-cauchy-approximation-Metric-Space

  is-cauchy-approximation-map-Convergent-cauchy-approximation-Metric-Space :
    is-cauchy-approximation-Metric-Space
      A
      map-Convergent-cauchy-approximation-Metric-Space
  is-cauchy-approximation-map-Convergent-cauchy-approximation-Metric-Space =
    is-cauchy-approximation-map-cauchy-approximation-Metric-Space
      A
      approximation-Convergent-cauchy-approximation-Metric-Space

  limit-Convergent-cauchy-approximation-Metric-Space : type-Metric-Space A
  limit-Convergent-cauchy-approximation-Metric-Space = pr1 (pr2 f)

  is-limit-limit-Convergent-cauchy-approximation-Metric-Space :
    (ε δ : ℚ⁺) →
    neighborhood-Metric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-Convergent-cauchy-approximation-Metric-Space ε)
      ( limit-Convergent-cauchy-approximation-Metric-Space)
  is-limit-limit-Convergent-cauchy-approximation-Metric-Space = pr2 (pr2 f)

  is-approximate-limit-Convergent-cauchy-approximation-Metric-Space :
    (ε δ : ℚ⁺) (H : le-ℚ⁺ δ ε) →
    neighborhood-Metric-Space
      ( A)
      ( ε)
      ( map-Convergent-cauchy-approximation-Metric-Space δ)
      ( limit-Convergent-cauchy-approximation-Metric-Space)
  is-approximate-limit-Convergent-cauchy-approximation-Metric-Space =
    is-approximate-is-limit-cauchy-approximation-Premetric-Space
      ( premetric-Metric-Space A)
      ( approximation-Convergent-cauchy-approximation-Metric-Space)
      ( limit-Convergent-cauchy-approximation-Metric-Space)
      ( is-limit-limit-Convergent-cauchy-approximation-Metric-Space)
```

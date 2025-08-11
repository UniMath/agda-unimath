# Convergent Cauchy approximations in metric spaces

```agda
module metric-spaces.convergent-cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-premetric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [Cauchy approximation](metric-spaces.cauchy-approximations-metric-spaces.md)
in a [metric space](metric-spaces.metric-spaces.md) is
{{#concept "convergent" Disambiguation="Cauchy approximation in a metric space" agda=is-convergent-cauchy-approximation-Metric-Space}}
if it has a
[limit](metric-spaces.limits-of-cauchy-approximations-premetric-spaces.md).
Because limits of Cauchy approximations in metric spaces are unique, this is a
[subtype](foundation.subtypes.md) of the type of Cauchy approximations.

## Definitions

### The property of being a convergent Cauchy approximation in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  where

  is-limit-cauchy-approximation-prop-Metric-Space :
    type-Metric-Space A → Prop l2
  is-limit-cauchy-approximation-prop-Metric-Space =
    is-limit-cauchy-approximation-prop-Premetric-Space
      ( premetric-Metric-Space A)
      ( f)

  is-limit-cauchy-approximation-Metric-Space :
    type-Metric-Space A → UU l2
  is-limit-cauchy-approximation-Metric-Space =
    is-limit-cauchy-approximation-Premetric-Space
      ( premetric-Metric-Space A)
      ( f)

  is-convergent-cauchy-approximation-Metric-Space : UU (l1 ⊔ l2)
  is-convergent-cauchy-approximation-Metric-Space =
    Σ ( type-Metric-Space A)
      ( is-limit-cauchy-approximation-Metric-Space)

  abstract
    is-prop-is-convergent-cauchy-approximation-Metric-Space :
      is-prop is-convergent-cauchy-approximation-Metric-Space
    is-prop-is-convergent-cauchy-approximation-Metric-Space =
      is-prop-all-elements-equal
        ( λ x y →
          eq-type-subtype
            ( is-limit-cauchy-approximation-prop-Premetric-Space
              ( premetric-Metric-Space A)
              ( f))
            ( all-elements-equal-is-limit-cauchy-approximation-triangular-symmetric-extensional-Premetric-Space
              ( premetric-Metric-Space A)
              ( is-symmetric-structure-Metric-Space A)
              ( is-triangular-structure-Metric-Space A)
              ( is-extensional-structure-Metric-Space A)
              ( f)
              ( pr2 x)
              ( pr2 y)))

  is-convergent-prop-cauchy-approximation-Metric-Space : Prop (l1 ⊔ l2)
  is-convergent-prop-cauchy-approximation-Metric-Space =
    is-convergent-cauchy-approximation-Metric-Space ,
    is-prop-is-convergent-cauchy-approximation-Metric-Space
```

### The type of convergent Cauchy approximations in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  convergent-cauchy-approximation-Metric-Space : UU (l1 ⊔ l2)
  convergent-cauchy-approximation-Metric-Space =
    type-subtype (is-convergent-prop-cauchy-approximation-Metric-Space A)
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : convergent-cauchy-approximation-Metric-Space A)
  where

  approximation-convergent-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space A
  approximation-convergent-cauchy-approximation-Metric-Space = pr1 f

  map-convergent-cauchy-approximation-Metric-Space : ℚ⁺ → type-Metric-Space A
  map-convergent-cauchy-approximation-Metric-Space =
    map-cauchy-approximation-Metric-Space
      A
      approximation-convergent-cauchy-approximation-Metric-Space

  is-cauchy-approximation-map-convergent-cauchy-approximation-Metric-Space :
    (ε δ : ℚ⁺) →
    neighborhood-Metric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-convergent-cauchy-approximation-Metric-Space ε)
      ( map-convergent-cauchy-approximation-Metric-Space δ)
  is-cauchy-approximation-map-convergent-cauchy-approximation-Metric-Space =
    is-cauchy-approximation-map-cauchy-approximation-Metric-Space
      A
      approximation-convergent-cauchy-approximation-Metric-Space

  limit-convergent-cauchy-approximation-Metric-Space : type-Metric-Space A
  limit-convergent-cauchy-approximation-Metric-Space = pr1 (pr2 f)

  is-limit-limit-convergent-cauchy-approximation-Metric-Space :
    (ε δ : ℚ⁺) →
    neighborhood-Metric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-convergent-cauchy-approximation-Metric-Space ε)
      ( limit-convergent-cauchy-approximation-Metric-Space)
  is-limit-limit-convergent-cauchy-approximation-Metric-Space = pr2 (pr2 f)
```

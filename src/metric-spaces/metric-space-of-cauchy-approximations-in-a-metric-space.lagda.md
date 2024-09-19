# The standard metric space of cauchy approximations in a metric space

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The type of
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
a [metric space](metric-spaces.metric-spaces.md) `A` inherits the
[metric substructure](metric-spaces.subspaces-metric-spaces.md) of the constant
[product structure](metric-spaces.dependent-products-metric-spaces.md) over `A`.

This is the
{{#concept "metric space of cauchy approximations in a metric space" Agda=metric-space-cauchy-approsimxations-Metric-Space}}.

## Definitions

### The metric space of cauchy approximations in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  metric-space-cauchy-approximations-Metric-Space : Metric-Space (l1 ⊔ l2) l2
  metric-space-cauchy-approximations-Metric-Space =
    subspace-Metric-Space
      ( Π-Metric-Space ℚ⁺ (λ _ → A))
      ( is-cauchy-approximation-prop-Metric-Space A)
```

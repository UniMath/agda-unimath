# Metrics of metric spaces are uniformly continuous

```agda
module metric-spaces.metrics-of-metric-spaces-are-uniformly-continuous where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import foundation.dependent-pair-types
open import real-numbers.distance-real-numbers
open import foundation.existential-quantification
open import metric-spaces.metric-spaces
open import metric-spaces.metrics-of-metric-spaces
open import foundation.universe-levels
open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.metrics
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

If `ρ` [is a metric](metric-spaces.metrics-of-metric-spaces.md) of the
[metric space](metric-spaces.metric-spaces.md) `M`, then it is a
[uniformly continuous map](metric-spaces.uniformly-continuous-functions-metric-spaces.md)
from the
[product metric space](metric-spaces.cartesian-products-metric-spaces.md)
`M × M` to the metric space of
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md).

## Proof

```agda
module _
  {l1 l2 l3 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space M))
  (is-metric-M-ρ : is-metric-of-Metric-Space M ρ)
  where

  is-uniformly-continuous-metric-of-Metric-Space :
    is-uniformly-continuous-function-Metric-Space
      ( product-Metric-Space M M)
      ( metric-space-ℝ⁰⁺ l3)
      ( ind-Σ ρ)
  is-uniformly-continuous-metric-of-Metric-Space =
    intro-exists
      ( modulus-le-double-le-ℚ⁺)
      ( λ (x , y) ε (x' , y') (Nε'xx' , Nε'yy') →
        neighborhood-dist-ℝ ε (real-ℝ⁰⁺ (ρ x y)) (real-ℝ⁰⁺ (ρ x' y'))
          {!  transitive-leq-ℝ !})

```

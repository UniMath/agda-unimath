# Rational Cauchy approximations

```agda
module metric-spaces.rational-cauchy-approximations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

{{#concept "Rational Cauchy approximations" Agda=cauchy-approximation-ℚ}} are
[Cauchy approximations](metric-spaces.cauchy-approximations-metric-spaces.md) in
the
[metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md).

## Definitions

### The type of rational Cauchy approximations

```agda
cauchy-approximation-ℚ : UU lzero
cauchy-approximation-ℚ =
  cauchy-approximation-Metric-Space metric-space-ℚ

map-cauchy-approximation-ℚ : cauchy-approximation-ℚ → ℚ⁺ → ℚ
map-cauchy-approximation-ℚ =
  map-cauchy-approximation-Metric-Space
    metric-space-ℚ

is-cauchy-map-cauchy-approximation-ℚ :
  (f : cauchy-approximation-ℚ) →
  is-cauchy-approximation-Metric-Space
    ( metric-space-ℚ)
    ( map-cauchy-approximation-ℚ f)
is-cauchy-map-cauchy-approximation-ℚ =
  is-cauchy-approximation-map-cauchy-approximation-Metric-Space
    metric-space-ℚ
```

## Properties

### The distance between two values `f ε` and `f δ` of a rational Cauchy approximation is bounded by `ε + δ`

```agda
bound-dist-map-cauchy-approximation-ℚ :
  (f : cauchy-approximation-ℚ) →
  (ε δ : ℚ⁺) →
  leq-ℚ
    ( rational-dist-ℚ
      ( map-cauchy-approximation-ℚ f ε)
      ( map-cauchy-approximation-ℚ f δ))
    ( rational-ℚ⁺ (ε +ℚ⁺ δ))
bound-dist-map-cauchy-approximation-ℚ f ε δ =
  leq-dist-neighborhood-ℚ
    ( ε +ℚ⁺ δ)
    ( map-cauchy-approximation-ℚ f ε)
    ( map-cauchy-approximation-ℚ f δ)
    ( is-cauchy-map-cauchy-approximation-ℚ f ε δ)
```

### Any rational Cauchy approximation has a limit in the reals

```agda
real-limit-cauchy-approximation-ℚ : cauchy-approximation-ℚ → ℝ lzero
real-limit-cauchy-approximation-ℚ f =
  limit-cauchy-approximation-Complete-Metric-Space
    ( complete-metric-space-ℝ lzero)
    ( map-cauchy-approximation-short-function-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ lzero)
      ( short-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℝ lzero)
        ( isometry-metric-space-real-ℚ))
      ( f))
```

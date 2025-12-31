# The binary minimum of real numbers is a short function

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.short-map-binary-minimum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.short-maps-metric-spaces

open import real-numbers.binary-maximum-real-numbers
open import real-numbers.binary-minimum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.isometry-negation-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.short-map-binary-maximum-real-numbers
```

</details>

## Idea

For any `a : ℝ`, the
[binary minimum](real-numbers.binary-minimum-real-numbers.md) with `a` is a
[short function](metric-spaces.short-maps-metric-spaces.md) `ℝ → ℝ` for the
[standard real metric structure](real-numbers.metric-space-of-real-numbers.md).

## Proof

```agda
module _
  {l1 l2 : Level} (x : ℝ l1)
  where

  abstract opaque
    unfolding min-ℝ

    is-short-map-left-min-ℝ :
      is-short-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( min-ℝ x)
    is-short-map-left-min-ℝ =
      is-short-comp-is-short-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( metric-space-ℝ (l1 ⊔ l2))
        ( neg-ℝ)
        ( λ y → max-ℝ (neg-ℝ x) (neg-ℝ y))
        ( is-short-neg-ℝ)
        ( is-short-comp-is-short-map-Metric-Space
          ( metric-space-ℝ l2)
          ( metric-space-ℝ l2)
          ( metric-space-ℝ (l1 ⊔ l2))
          ( max-ℝ (neg-ℝ x))
          ( neg-ℝ)
          ( is-short-map-left-max-ℝ (neg-ℝ x))
          ( is-short-neg-ℝ))

  short-left-min-ℝ :
    short-map-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
  short-left-min-ℝ = (min-ℝ x , is-short-map-left-min-ℝ)
```

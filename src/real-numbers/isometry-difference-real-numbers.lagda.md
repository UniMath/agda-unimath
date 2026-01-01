# The difference isometry on real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.isometry-difference-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.isometry-negation-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
```

</details>

## Idea

[Subtracting](real-numbers.difference-real-numbers.md) from a fixed
[real number](real-numbers.dedekind-real-numbers.md) is an
[isometry](metric-spaces.isometries-metric-spaces.md) from the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md) to
itself.

## Definition

```agda
module _
  {l1 l2 : Level} (x : ℝ l1)
  where

  abstract
    is-isometry-left-diff-ℝ :
      is-isometry-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( diff-ℝ x)
    is-isometry-left-diff-ℝ =
      is-isometry-comp-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( add-ℝ x)
        ( neg-ℝ)
        ( is-isometry-left-add-ℝ x)
        ( is-isometry-neg-ℝ)

  isometry-left-diff-ℝ :
    isometry-Metric-Space (metric-space-ℝ l2) (metric-space-ℝ (l1 ⊔ l2))
  isometry-left-diff-ℝ = (diff-ℝ x , is-isometry-left-diff-ℝ)

  short-map-left-diff-ℝ :
    short-map-Metric-Space (metric-space-ℝ l2) (metric-space-ℝ (l1 ⊔ l2))
  short-map-left-diff-ℝ =
    short-map-isometry-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
      ( isometry-left-diff-ℝ)

  uniformly-continuous-map-left-diff-ℝ :
    uniformly-continuous-map-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
  uniformly-continuous-map-left-diff-ℝ =
    uniformly-continuous-map-isometry-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
      ( isometry-left-diff-ℝ)
```

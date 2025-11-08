# The located metric space of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.located-metric-space-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import metric-spaces.located-metric-spaces
open import metric-spaces.metrics-of-metric-spaces
open import real-numbers.distance-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import foundation.universe-levels
open import foundation.dependent-pair-types
```

## Idea

The [metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)
is [located](metric-spaces.located-metric-spaces.md).

## Definition

```agda
abstract
  is-located-metric-space-ℝ :
    (l : Level) → is-located-Metric-Space (metric-space-ℝ l)
  is-located-metric-space-ℝ l =
    is-located-is-metric-of-Metric-Space
      ( metric-space-ℝ l)
      ( nonnegative-dist-ℝ)
      ( dist-is-metric-of-metric-space-ℝ l)

located-metric-space-ℝ : (l : Level) → Located-Metric-Space (lsuc l) l
located-metric-space-ℝ l = (metric-space-ℝ l , is-located-metric-space-ℝ l)
```

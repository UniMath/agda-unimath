# The metric space of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.metric-space-of-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.metric-spaces

open import real-numbers.nonnegative-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

The [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) form a
[subspace](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
metric-space-ℝ⁰⁺ : (l : Level) → Metric-Space (lsuc l) l
metric-space-ℝ⁰⁺ l = metric-space-subset-ℝ (is-nonnegative-prop-ℝ {l})
```

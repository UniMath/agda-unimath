# Convergent series of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.convergent-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-metric-abelian-groups

open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.series-real-numbers
```

</details>

## Idea

A [series](real-numbers.series-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md)
{{#concepts "converges" Disambiguation="series of real numbers" Agda=is-convergent-series-ℝ}}
to `x` if the sequence of its partial sums
[converges](metric-spaces.limits-of-sequences-metric-spaces.md) to `x` in the
[standard metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
is-sum-prop-series-ℝ : {l : Level} → series-ℝ l → ℝ l → Prop l
is-sum-prop-series-ℝ = is-sum-prop-series-Metric-Ab

is-sum-series-ℝ : {l : Level} → series-ℝ l → ℝ l → UU l
is-sum-series-ℝ = is-sum-series-Metric-Ab
```

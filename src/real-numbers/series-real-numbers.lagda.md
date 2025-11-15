# Series of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.series-metric-abelian-groups

open import foundation.universe-levels

open import lists.sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-additive-group-of-real-numbers
```

</details>

## Idea

A {{#concept "series" Disambiguation="of real numbers" Agda=series-ℝ}} of
[real numbers](real-numbers.dedekind-real-numbers.md) is an infinite sum
$$∑_{n=0}^∞ a_n$$, which is evaluated for convergence in the
[metric abelian group of real numbers](real-numbers.metric-additive-group-of-real-numbers.md).

## Definition

```agda
series-ℝ : (l : Level) → UU (lsuc l)
series-ℝ l = series-Metric-Ab (metric-ab-add-ℝ l)

series-terms-ℝ : {l : Level} → sequence (ℝ l) → series-ℝ l
series-terms-ℝ = series-terms-Metric-Ab

terms-series-ℝ : {l : Level} → series-ℝ l → sequence (ℝ l)
terms-series-ℝ = term-series-Metric-Ab
```

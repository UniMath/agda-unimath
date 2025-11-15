# Series in the real numbers

```agda
module analysis.series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.series-complete-metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import foundation.universe-levels

open import lists.sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-additive-group-of-real-numbers
```

</details>

## Idea

A {{#concept "series" Disambiguation="of real numbers" Agda=series-ℝ}} in the
[real numbers](real-numbers.dedekind-real-numbers.md) is a
[series](analysis.series-metric-abelian-groups.md) in the
[metric additive group of real numbers](real-numbers.metric-additive-group-of-real-numbers.md).

## Definition

```agda
series-ℝ : (l : Level) → UU (lsuc l)
series-ℝ l = series-Complete-Metric-Ab (complete-metric-ab-add-ℝ l)

series-terms-ℝ : {l : Level} → sequence (ℝ l) → series-ℝ l
series-terms-ℝ = series-terms-Metric-Ab

term-series-ℝ : {l : Level} → series-ℝ l → sequence (ℝ l)
term-series-ℝ = term-series-Metric-Ab

partial-sum-series-ℝ : {l : Level} → series-ℝ l → sequence (ℝ l)
partial-sum-series-ℝ {l} = partial-sum-series-Metric-Ab (metric-ab-add-ℝ l)
```

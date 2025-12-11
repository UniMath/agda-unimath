# Series in the real numbers

```agda
module analysis.series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.series-complete-metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
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
series-ℝ l = series-Metric-Ab (metric-ab-add-ℝ l)

series-terms-ℝ : {l : Level} → sequence (ℝ l) → series-ℝ l
series-terms-ℝ = series-terms-Metric-Ab

term-series-ℝ : {l : Level} → series-ℝ l → sequence (ℝ l)
term-series-ℝ = term-series-Metric-Ab

partial-sum-series-ℝ : {l : Level} → series-ℝ l → sequence (ℝ l)
partial-sum-series-ℝ {l} = partial-sum-series-Metric-Ab
```

## Properties

### Dropping terms from a series

```agda
module _
  {l : Level}
  where

  drop-series-ℝ : ℕ → series-ℝ l → series-ℝ l
  drop-series-ℝ = drop-series-Metric-Ab
```

### The partial sums of a series after dropping terms

```agda
module _
  {l : Level}
  where

  abstract
    partial-sum-drop-series-ℝ :
      (n : ℕ) (σ : series-ℝ l) (i : ℕ) →
      partial-sum-series-ℝ (drop-series-ℝ n σ) i ＝
      partial-sum-series-ℝ σ (n +ℕ i) -ℝ partial-sum-series-ℝ σ n
    partial-sum-drop-series-ℝ = partial-sum-drop-series-Metric-Ab
```

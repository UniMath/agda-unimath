# Series in the real numbers

```agda
module analysis.series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.series-complete-metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import lists.sequences

open import order-theory.monotonic-sequences-posets

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-additive-group-of-real-numbers
open import real-numbers.nonnegative-real-numbers
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
partial-sum-series-ℝ {l} = partial-sum-series-Metric-Ab
```

## Properties

### If the terms of a series of real numbers are nonnegative, the partial sums are monotonic

```agda
abstract
  is-monotonic-partial-sum-is-nonnegative-term-series-ℝ :
    {l : Level} (σ : series-ℝ l) →
    ((n : ℕ) → is-nonnegative-ℝ (term-series-ℝ σ n)) →
    is-monotonic-sequence-Poset (ℝ-Poset l) (partial-sum-series-ℝ σ)
  is-monotonic-partial-sum-is-nonnegative-term-series-ℝ {l} σ H =
    is-monotonic-sequence-is-increasing-Poset
      ( ℝ-Poset l)
      ( partial-sum-series-ℝ σ)
      ( λ n → leq-left-add-real-ℝ⁰⁺ _ (term-series-ℝ σ n , H n))
```

# Series of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.series-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-metric-abelian-groups
open import analysis.series-metric-abelian-groups

open import elementary-number-theory.addition-nonnegative-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.metric-additive-group-of-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import order-theory.increasing-sequences-posets
open import order-theory.order-preserving-maps-posets
```

</details>

## Idea

A {{#concept "series" Disambiguation="in ℚ" Agda=series-ℚ}} of
[rational numbers](elementary-number-theory.rational-numbers.md) is a
[series](analysis.series-metric-abelian-groups.md) in the
[metric additive group of rational numbers](elementary-number-theory.metric-additive-group-of-rational-numbers.md)

## Definition

```agda
series-ℚ : UU lzero
series-ℚ = series-Metric-Ab metric-ab-add-ℚ

series-terms-ℚ : sequence ℚ → series-ℚ
series-terms-ℚ = series-terms-Metric-Ab

partial-sum-series-ℚ : series-ℚ → ℕ → ℚ
partial-sum-series-ℚ = partial-sum-series-Metric-Ab

term-series-ℚ : series-ℚ → ℕ → ℚ
term-series-ℚ = term-series-Metric-Ab
```

## Properties

### The proposition that a series converges to a sum

```agda
is-sum-prop-series-ℚ : series-ℚ → ℚ → Prop lzero
is-sum-prop-series-ℚ = is-sum-prop-series-Metric-Ab

is-sum-series-ℚ : series-ℚ → ℚ → UU lzero
is-sum-series-ℚ = is-sum-series-Metric-Ab
```

### The proposition that a series grows without bound

```agda
partial-sum-stays-above-prop-series-ℚ : series-ℚ → ℚ → ℕ → Prop lzero
partial-sum-stays-above-prop-series-ℚ σ q n =
  Π-Prop ℕ (λ k → leq-ℕ-Prop n k ⇒ leq-ℚ-Prop q (partial-sum-series-ℚ σ k))

grows-without-bound-prop-series-ℚ : series-ℚ → Prop lzero
grows-without-bound-prop-series-ℚ σ =
  Π-Prop ℚ (λ q → ∃ ℕ (partial-sum-stays-above-prop-series-ℚ σ q))

grows-without-bound-series-ℚ : series-ℚ → UU lzero
grows-without-bound-series-ℚ σ =
  type-Prop (grows-without-bound-prop-series-ℚ σ)
```

### If all elements of a series are nonnegative, its partial sums are increasing

```agda
abstract
  is-increasing-partial-sum-is-nonnegative-term-series-ℚ :
    (σ : series-ℚ) → ((n : ℕ) → is-nonnegative-ℚ (term-series-ℚ σ n)) →
    is-increasing-sequence-Poset ℚ-Poset (partial-sum-series-ℚ σ)
  is-increasing-partial-sum-is-nonnegative-term-series-ℚ σ H =
    is-increasing-leq-succ-sequence-Poset
      ( ℚ-Poset)
      ( partial-sum-series-ℚ σ)
      ( λ n →
        is-inflationary-map-right-add-rational-ℚ⁰⁺
          ( term-series-ℚ σ n , H n)
          ( partial-sum-series-ℚ σ n))
```

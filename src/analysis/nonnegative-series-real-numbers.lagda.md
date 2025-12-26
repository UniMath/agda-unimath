# Nonnegative series in the real numbers

```agda
module analysis.nonnegative-series-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.series-real-numbers

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.increasing-sequences-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

A [series in ℝ](analysis.series-real-numbers.md) is
{{#concept "nonnegative" Disambiguation="series in ℝ" Agda=is-nonnegative-series-ℝ}}
if each of its terms is [nonnegative](real-numbers.nonnegative-real-numbers.md).

## Definition

```agda
is-nonnegative-prop-series-ℝ : {l : Level} → series-ℝ l → Prop l
is-nonnegative-prop-series-ℝ σ =
  Π-Prop ℕ (λ n → is-nonnegative-prop-ℝ (term-series-ℝ σ n))

is-nonnegative-series-ℝ : {l : Level} → series-ℝ l → UU l
is-nonnegative-series-ℝ σ = type-Prop (is-nonnegative-prop-series-ℝ σ)
```

### If the terms of a series of real numbers are nonnegative, the partial sums are monotonic

```agda
abstract
  is-increasing-partial-sum-is-nonnegative-term-series-ℝ :
    {l : Level} (σ : series-ℝ l) →
    is-nonnegative-series-ℝ σ →
    is-increasing-sequence-Poset (ℝ-Poset l) (partial-sum-series-ℝ σ)
  is-increasing-partial-sum-is-nonnegative-term-series-ℝ {l} σ H =
    is-increasing-leq-succ-sequence-Poset
      ( ℝ-Poset l)
      ( partial-sum-series-ℝ σ)
      ( λ n → leq-left-add-real-ℝ⁰⁺ _ (term-series-ℝ σ n , H n))
```

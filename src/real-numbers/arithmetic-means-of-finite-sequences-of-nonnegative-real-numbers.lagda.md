# Arithmetic means of finite sequences of nonnegative real numbers

```agda
module real-numbers.arithmetic-means-of-finite-sequences-of-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import lists.finite-sequences

open import real-numbers.arithmetic-means-of-finite-sequences-of-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.sums-of-finite-sequences-of-nonnegative-real-numbers
```

</details>

## Idea

The
{{#concept "arithmetic mean" WDID=Q19033 WD="arithmetic mean" Disambiguation="of a finite sequence of real numbers" Agda=mean-fin-sequence-ℝ}}
of a nonempty [finite sequence](lists.finite-sequences.md) of
[nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) `a₁, ..., aₙ` is the
[reciprocal](elementary-number-theory.unit-fractions-rational-numbers.md) of `n`
[times](real-numbers.multiplication-real-numbers.md) the
[sum](real-numbers.sums-of-finite-sequences-of-nonnegative-real-numbers.md) of
the `aᵢ`.

## Definition

```agda
module _
  {l : Level}
  (n : ℕ⁺)
  (a : fin-sequence (ℝ⁰⁺ l) (nat-ℕ⁺ n))
  where

  real-arithmetic-mean-fin-sequence-ℝ⁰⁺ : ℝ l
  real-arithmetic-mean-fin-sequence-ℝ⁰⁺ =
    arithmetic-mean-fin-sequence-ℝ n (real-ℝ⁰⁺ ∘ a)

  abstract
    is-nonnegative-real-arithmetic-mean-fin-sequence-ℝ⁰⁺ :
      is-nonnegative-ℝ real-arithmetic-mean-fin-sequence-ℝ⁰⁺
    is-nonnegative-real-arithmetic-mean-fin-sequence-ℝ⁰⁺ =
      is-nonnegative-mul-ℝ
        ( preserves-is-nonnegative-real-ℚ
          ( is-nonnegative-is-positive-ℚ
            ( is-positive-rational-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ n))))
        ( is-nonnegative-real-sum-fin-sequence-ℝ⁰⁺ (nat-ℕ⁺ n) a)

  arithmetic-mean-fin-sequence-ℝ⁰⁺ : ℝ⁰⁺ l
  arithmetic-mean-fin-sequence-ℝ⁰⁺ =
    ( real-arithmetic-mean-fin-sequence-ℝ⁰⁺ ,
      is-nonnegative-real-arithmetic-mean-fin-sequence-ℝ⁰⁺)
```

# Arithmetic means of finite sequences of real numbers

```agda
module real-numbers.arithmetic-means-of-finite-sequences-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers
```

</details>

## Idea

The
{{#concept "arithmetic mean" WDID=Q19033 WD="arithmetic mean" Disambiguation="of a finite sequence of real numbers" Agda=arithmetic-mean-fin-sequence-ℝ}}
of a nonempty [finite sequence](lists.finite-sequences.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) `a₁, ..., aₙ` is the
[reciprocal](elementary-number-theory.unit-fractions-rational-numbers.md) of `n`
[times](real-numbers.multiplication-real-numbers.md) the
[sum](real-numbers.sums-of-finite-sequences-of-real-numbers.md) of the `aᵢ`.

## Definition

```agda
module _
  {l : Level}
  (n : ℕ⁺)
  (a : fin-sequence (ℝ l) (nat-ℕ⁺ n))
  where

  arithmetic-mean-fin-sequence-ℝ : ℝ l
  arithmetic-mean-fin-sequence-ℝ =
    real-ℚ (reciprocal-rational-ℕ⁺ n) *ℝ sum-fin-sequence-ℝ (nat-ℕ⁺ n) a
```

## Properties

### Permuting the elements of a finite sequence preserves the mean

```agda
module _
  {l : Level}
  (n : ℕ⁺)
  (σ : Permutation (nat-ℕ⁺ n))
  (a : fin-sequence (ℝ l) (nat-ℕ⁺ n))
  where

  abstract
    preserves-arithmetic-mean-permutation-fin-sequence-ℝ :
      arithmetic-mean-fin-sequence-ℝ n a ＝
      arithmetic-mean-fin-sequence-ℝ n (a ∘ map-equiv σ)
    preserves-arithmetic-mean-permutation-fin-sequence-ℝ =
      ap-mul-ℝ refl (preserves-sum-permutation-fin-sequence-ℝ (nat-ℕ⁺ n) σ a)
```

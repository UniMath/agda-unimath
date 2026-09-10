# Unit fractions in the real numbers

```agda
module real-numbers.unit-fractions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A {{#concept "unit fraction" Disambiguation="in the real numbers"}} in the
[real numbers](real-numbers.dedekind-real-numbers.md) is the
[real embedding](real-numbers.rational-real-numbers.md) of a
[rational unit fraction](elementary-number-theory.unit-fractions-rational-numbers.md).

## Definition

```agda
positive-reciprocal-real-ℕ⁺ : ℕ⁺ → ℝ⁺ lzero
positive-reciprocal-real-ℕ⁺ n =
  positive-real-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ n)

nonnegative-reciprocal-real-ℕ⁺ : ℕ⁺ → ℝ⁰⁺ lzero
nonnegative-reciprocal-real-ℕ⁺ n =
  nonnegative-ℝ⁺ (positive-reciprocal-real-ℕ⁺ n)

reciprocal-real-ℕ⁺ : ℕ⁺ → ℝ lzero
reciprocal-real-ℕ⁺ n = real-ℝ⁺ (positive-reciprocal-real-ℕ⁺ n)

positive-reciprocal-real-succ-ℕ : ℕ → ℝ⁺ lzero
positive-reciprocal-real-succ-ℕ n =
  positive-reciprocal-real-ℕ⁺ (succ-nonzero-ℕ' n)

nonnegative-reciprocal-real-succ-ℕ : ℕ → ℝ⁰⁺ lzero
nonnegative-reciprocal-real-succ-ℕ n =
  nonnegative-ℝ⁺ (positive-reciprocal-real-succ-ℕ n)

reciprocal-real-succ-ℕ : ℕ → ℝ lzero
reciprocal-real-succ-ℕ n = real-ℝ⁺ (positive-reciprocal-real-succ-ℕ n)
```

## Properties

### Inverse laws

```agda
module _
  (n : ℕ⁺)
  where abstract

  left-inverse-law-reciprocal-real-ℕ⁺ :
    reciprocal-real-ℕ⁺ n *ℝ real-ℕ⁺ n ＝ one-ℝ
  left-inverse-law-reciprocal-real-ℕ⁺ =
    ( mul-real-ℚ _ _) ∙
    ( ap real-ℚ (left-inverse-law-reciprocal-rational-ℕ⁺ n))

module _
  (n : ℕ)
  where abstract

  left-inverse-law-reciprocal-real-succ-ℕ :
    reciprocal-real-succ-ℕ n *ℝ real-ℕ (succ-ℕ n) ＝ one-ℝ
  left-inverse-law-reciprocal-real-succ-ℕ =
    left-inverse-law-reciprocal-real-ℕ⁺ (succ-nonzero-ℕ' n)
```

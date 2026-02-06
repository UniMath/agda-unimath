# Iterated halving of the difference between real numbers

```agda
module real-numbers.iterated-halving-difference-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-positive-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.real-sequences-approximating-zero
```

</details>

## Idea

Given two [real numbers](real-numbers.dedekind-real-numbers.md) `a` and `b` with
`a` [less than or equal to](real-numbers.inequality-real-numbers.md) `b`,
$(b-a)/2^n$ is a sequence of
[nonnegative](real-numbers.nonnegative-real-numbers.md) real numbers
[approaching zero](real-numbers.real-sequences-approximating-zero.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  {a : ℝ l1}
  {b : ℝ l2}
  (a≤b : leq-ℝ a b)
  where

  nonnegative-iterated-half-diff-leq-ℝ : ℕ → ℝ⁰⁺ (l1 ⊔ l2)
  nonnegative-iterated-half-diff-leq-ℝ n =
    nonnegative-diff-leq-ℝ a≤b *ℝ⁰⁺
    nonnegative-real-ℚ⁺ (power-ℚ⁺ n one-half-ℚ⁺)

  iterated-half-diff-leq-ℝ : ℕ → ℝ (l1 ⊔ l2)
  iterated-half-diff-leq-ℝ n = real-ℝ⁰⁺ (nonnegative-iterated-half-diff-leq-ℝ n)
```

## Properties

### `½ ((b-a)/2ⁿ) = (b-a)/2ⁿ⁺¹`

```agda
module _
  {l1 l2 : Level}
  {a : ℝ l1}
  {b : ℝ l2}
  (a≤b : leq-ℝ a b)
  where

  abstract
    mul-one-half-iterated-half-diff-leq-ℝ :
      (n : ℕ) →
      one-half-ℝ *ℝ iterated-half-diff-leq-ℝ a≤b n ＝
      iterated-half-diff-leq-ℝ a≤b (succ-ℕ n)
    mul-one-half-iterated-half-diff-leq-ℝ n =
      equational-reasoning
        one-half-ℝ *ℝ iterated-half-diff-leq-ℝ a≤b n
        ＝ (b -ℝ a) *ℝ (one-half-ℝ *ℝ real-ℚ⁺ (power-ℚ⁺ n one-half-ℚ⁺))
          by left-swap-mul-ℝ _ _ _
        ＝ (b -ℝ a) *ℝ (real-ℚ⁺ (one-half-ℚ⁺ *ℚ⁺ power-ℚ⁺ n one-half-ℚ⁺))
          by ap-mul-ℝ refl (mul-real-ℚ _ _)
        ＝ (b -ℝ a) *ℝ (real-ℚ⁺ (power-ℚ⁺ (succ-ℕ n) one-half-ℚ⁺))
          by ap-mul-ℝ refl (ap real-ℚ⁺ (inv (power-succ-ℚ⁺' n one-half-ℚ⁺)))
```

### `(b-a)/2ⁿ` approaches 0 as `n` grows without bound

```agda
module _
  {l1 l2 : Level}
  {a : ℝ l1}
  {b : ℝ l2}
  (a≤b : leq-ℝ a b)
  where

  abstract
    is-zero-limit-iterated-half-diff-leq-ℝ :
      is-zero-limit-sequence-ℝ (iterated-half-diff-leq-ℝ a≤b)
    is-zero-limit-iterated-half-diff-leq-ℝ =
      preserves-is-zero-limit-left-mul-sequence-ℝ
        ( b -ℝ a)
        ( _)
        ( is-zero-limit-real-is-zero-limit-sequence-ℚ _
          ( is-zero-limit-power-le-one-ℚ⁺
            ( one-half-ℚ⁺)
            ( le-one-half-one-ℚ)))
```

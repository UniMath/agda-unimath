# Unit fractions in the rational numbers types

```agda
module elementary-number-theory.unit-fractions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
```

</details>

## Idea

The {{#concept "unit fractions" WDID=Q255388 WD="unit fraction"}} are
[rational numbers](elementary-number-theory.rational-numbers.md) whose numerator
is 1 and whose denominator is a positive integer (or, equivalently, a positive
natural number).

## Definition

### Reciprocals of nonzero natural numbers

```agda
positive-reciprocal-rational-ℕ⁺ : ℕ⁺ → ℚ⁺
positive-reciprocal-rational-ℕ⁺ n = inv-ℚ⁺ (positive-rational-ℕ⁺ n)

reciprocal-rational-ℕ⁺ : ℕ⁺ → ℚ
reciprocal-rational-ℕ⁺ n = rational-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ n)
```

### If `m ≤ n`, the reciprocal of `n` is less than or equal to the reciprocal of `n`

```agda
abstract
  leq-reciprocal-rational-ℕ⁺ :
    (m n : ℕ⁺) → leq-ℕ⁺ m n →
    leq-ℚ (reciprocal-rational-ℕ⁺ n) (reciprocal-rational-ℕ⁺ m)
  leq-reciprocal-rational-ℕ⁺ (m , pos-m) (n , pos-n) m≤n =
    binary-tr
      ( leq-ℤ)
      ( left-unit-law-mul-ℤ (int-ℕ m))
      ( left-unit-law-mul-ℤ (int-ℕ n))
      ( leq-int-ℕ m n m≤n)
```

### If `m < n`, the reciprocal of `n` is less than the reciprocal of `n`

```agda
abstract
  le-reciprocal-rational-ℕ⁺ :
    (m n : ℕ⁺) → le-ℕ⁺ m n →
    le-ℚ⁺
      ( positive-reciprocal-rational-ℕ⁺ n)
      ( positive-reciprocal-rational-ℕ⁺ m)
  le-reciprocal-rational-ℕ⁺ (m , pos-m) (n , pos-n) m<n =
    binary-tr
      ( le-ℤ)
      ( left-unit-law-mul-ℤ (int-ℕ m))
      ( left-unit-law-mul-ℤ (int-ℕ n))
      ( le-natural-le-ℤ m n m<n)
```

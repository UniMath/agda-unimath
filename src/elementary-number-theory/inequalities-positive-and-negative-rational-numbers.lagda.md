# Inequalities between positive, negative, nonnegative, and nonpositive rational numbers

```agda
module elementary-number-theory.inequalities-positive-and-negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
```

</details>

## Idea

This page describes
[inequalities](elementary-number-theory.inequalities-rational-numbers.md) and
[strict inequalities](elementary-number-theory.strict-inequality-rational-numbers.md)
between [positive](elementary-number-theory.positive-rational-numbers.md),
[negative](elementary-number-theory.negative-rational-numbers.md),
[nonnegative](elementary-number-theory.nonnegative-rational-numbers.md), and
[nonpositive](elementary-number-theory.nonpositive-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md).

## Properties

### Inequalities between rational numbers with different signs

Some inequalities can be deduced directly from the sign of a rational number:
for example, every negative rational number is less than every nonnegative
rational number.

#### Any negative rational number is less than any nonnegative rational number

```agda
abstract
  le-negative-nonnegative-ℚ :
    (p : ℚ⁻) (q : ℚ⁰⁺) → le-ℚ (rational-ℚ⁻ p) (rational-ℚ⁰⁺ q)
  le-negative-nonnegative-ℚ (p , neg-p) (q , nonneg-q) =
    concatenate-le-leq-ℚ p zero-ℚ q
      ( le-zero-is-negative-ℚ neg-p)
      ( leq-zero-is-nonnegative-ℚ nonneg-q)

  leq-negative-nonnegative-ℚ :
    (p : ℚ⁻) (q : ℚ⁰⁺) → leq-ℚ (rational-ℚ⁻ p) (rational-ℚ⁰⁺ q)
  leq-negative-nonnegative-ℚ p q = leq-le-ℚ (le-negative-nonnegative-ℚ p q)
```

#### A nonpositive rational number is less than a positive rational number

```agda
abstract
  le-nonpositive-positive-ℚ :
    (p : ℚ⁰⁻) (q : ℚ⁺) → le-ℚ (rational-ℚ⁰⁻ p) (rational-ℚ⁺ q)
  le-nonpositive-positive-ℚ (p , nonpos-p) (q , pos-q) =
    concatenate-leq-le-ℚ p zero-ℚ q
      ( leq-zero-is-nonpositive-ℚ nonpos-p)
      ( le-zero-is-positive-ℚ pos-q)
```

#### A nonpositive rational number is less than or equal to a nonnegative rational number

```agda
abstract
  leq-nonpositive-nonnegative-ℚ :
    (p : ℚ⁰⁻) (q : ℚ⁰⁺) → leq-ℚ (rational-ℚ⁰⁻ p) (rational-ℚ⁰⁺ q)
  leq-nonpositive-nonnegative-ℚ (p , nonpos-p) (q , nonneg-q) =
    transitive-leq-ℚ p zero-ℚ q
      ( leq-zero-is-nonnegative-ℚ nonneg-q)
      ( leq-zero-is-nonpositive-ℚ nonpos-p)
```

### Inequalities showing the sign of a rational number

#### If `p < q` and `p` is nonnegative, then `q` is positive

```agda
abstract
  is-positive-le-ℚ⁰⁺ :
    (p : ℚ⁰⁺) (q : ℚ) → le-ℚ (rational-ℚ⁰⁺ p) q → is-positive-ℚ q
  is-positive-le-ℚ⁰⁺ (p , nonneg-p) q p<q =
    is-positive-le-zero-ℚ
      ( concatenate-leq-le-ℚ _ _ _ (leq-zero-is-nonnegative-ℚ nonneg-p) p<q)
```

#### If `p < q` and `q` is nonpositive, then `p` is negative

```agda
abstract
  is-negative-le-ℚ⁰⁻ :
    (q : ℚ⁰⁻) (p : ℚ) → le-ℚ p (rational-ℚ⁰⁻ q) → is-negative-ℚ p
  is-negative-le-ℚ⁰⁻ (q , nonpos-q) p p<q =
    is-negative-le-zero-ℚ
      ( concatenate-le-leq-ℚ p q zero-ℚ
        ( p<q)
        ( leq-zero-is-nonpositive-ℚ nonpos-q))
```

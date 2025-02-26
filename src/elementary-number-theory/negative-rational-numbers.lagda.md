# Negative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.positive-rational-numbers
```

</details>

## Idea

A [rational number](elementary-number-theory.rational-numbers.md) `x` is said to
be {{#concept "negative" Disambiguation="rational number" Agda=is-negative-ℚ}}
if its underlying fraction is negative.

Positive rational numbers are a [subsemigroup](group-theory.subsemigroups.md) of
the
[additive monoid of rational numbers](elementary-number-theory.additive-group-of-rational-numbers.md).

## Definitions

### The property of being a negative rational number

```agda
module _
  (x : ℚ)
  where

  is-positive-ℚ : UU lzero
  is-positive-ℚ = is-positive-fraction-ℤ (fraction-ℚ x)

  is-prop-is-positive-ℚ : is-prop is-positive-ℚ
  is-prop-is-positive-ℚ = is-prop-is-positive-fraction-ℤ (fraction-ℚ x)

  is-positive-prop-ℚ : Prop lzero
  pr1 is-positive-prop-ℚ = is-positive-ℚ
  pr2 is-positive-prop-ℚ = is-prop-is-positive-ℚ
```

### The type of positive rational numbers

```agda
positive-ℚ : UU lzero
positive-ℚ = type-subtype is-positive-prop-ℚ

ℚ⁺ : UU lzero
ℚ⁺ = positive-ℚ

module _
  (x : positive-ℚ)
  where

  rational-ℚ⁺ : ℚ
  rational-ℚ⁺ = pr1 x

  fraction-ℚ⁺ : fraction-ℤ
  fraction-ℚ⁺ = fraction-ℚ rational-ℚ⁺

  numerator-ℚ⁺ : ℤ
  numerator-ℚ⁺ = numerator-ℚ rational-ℚ⁺

  denominator-ℚ⁺ : ℤ
  denominator-ℚ⁺ = denominator-ℚ rational-ℚ⁺

  is-positive-rational-ℚ⁺ : is-positive-ℚ rational-ℚ⁺
  is-positive-rational-ℚ⁺ = pr2 x

  is-positive-fraction-ℚ⁺ : is-positive-fraction-ℤ fraction-ℚ⁺
  is-positive-fraction-ℚ⁺ = is-positive-rational-ℚ⁺

  is-positive-numerator-ℚ⁺ : is-positive-ℤ numerator-ℚ⁺
  is-positive-numerator-ℚ⁺ = is-positive-rational-ℚ⁺

  is-positive-denominator-ℚ⁺ : is-positive-ℤ denominator-ℚ⁺
  is-positive-denominator-ℚ⁺ = is-positive-denominator-ℚ rational-ℚ⁺

abstract
  eq-ℚ⁺ : {x y : ℚ⁺} → rational-ℚ⁺ x ＝ rational-ℚ⁺ y → x ＝ y
  eq-ℚ⁺ {x} {y} = eq-type-subtype is-positive-prop-ℚ
```

## Properties

### The positive rational numbers form a set

```agda
is-set-ℚ⁺ : is-set ℚ⁺
is-set-ℚ⁺ = is-set-type-subtype is-positive-prop-ℚ is-set-ℚ
```

### The rational image of a positive integer is positive

```agda
abstract
  is-positive-rational-ℤ :
    (x : ℤ) → is-positive-ℤ x → is-positive-ℚ (rational-ℤ x)
  is-positive-rational-ℤ x P = P

positive-rational-positive-ℤ : positive-ℤ → ℚ⁺
positive-rational-positive-ℤ (z , pos-z) = rational-ℤ z , pos-z

```

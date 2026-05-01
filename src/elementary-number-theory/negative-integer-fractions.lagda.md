# Negative integer fractions

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.negative-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-integers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

An [integer fraction](elementary-number-theory.integer-fractions.md) `x` is said
to be
{{#concept "negative" Disambiguation="integer fraction" Agda=is-negative-fraction-ℤ}}
if its numerator is a
[negative integer](elementary-number-theory.negative-integers.md).

## Definitions

### The property of being a negative integer fraction

```agda
module _
  (x : fraction-ℤ)
  where

  is-negative-fraction-ℤ : UU lzero
  is-negative-fraction-ℤ = is-negative-ℤ (numerator-fraction-ℤ x)

  is-prop-is-negative-fraction-ℤ : is-prop is-negative-fraction-ℤ
  is-prop-is-negative-fraction-ℤ =
    is-prop-is-negative-ℤ (numerator-fraction-ℤ x)
```

## Properties

### The negative of a positive integer fraction is negative

```agda
abstract
  is-negative-neg-positive-fraction-ℤ :
    (x : fraction-ℤ) → is-positive-fraction-ℤ x →
    is-negative-fraction-ℤ (neg-fraction-ℤ x)
  is-negative-neg-positive-fraction-ℤ _ = is-negative-neg-is-positive-ℤ
```

### The negative of a negative integer fraction is positive

```agda
abstract
  is-positive-neg-negative-fraction-ℤ :
    (x : fraction-ℤ) → is-negative-fraction-ℤ x →
    is-positive-fraction-ℤ (neg-fraction-ℤ x)
  is-positive-neg-negative-fraction-ℤ _ = is-positive-neg-is-negative-ℤ
```

### An integer fraction similar to a negative integer fraction is negative

```agda
is-negative-sim-fraction-ℤ :
  (x y : fraction-ℤ) (S : sim-fraction-ℤ x y) →
  is-negative-fraction-ℤ x →
  is-negative-fraction-ℤ y
is-negative-sim-fraction-ℤ x y S N =
  is-negative-right-factor-mul-positive-ℤ
    ( is-negative-eq-ℤ
      ( S ∙
        commutative-mul-ℤ (numerator-fraction-ℤ y) (denominator-fraction-ℤ x))
      ( is-negative-mul-negative-positive-ℤ
        ( N)
        ( is-positive-denominator-fraction-ℤ y)))
    ( is-positive-denominator-fraction-ℤ x)
```

### The reduced fraction of a negative integer fraction is negative

```agda
is-negative-reduce-fraction-ℤ :
  {x : fraction-ℤ} (P : is-negative-fraction-ℤ x) →
  is-negative-fraction-ℤ (reduce-fraction-ℤ x)
is-negative-reduce-fraction-ℤ {x} =
  is-negative-sim-fraction-ℤ
    ( x)
    ( reduce-fraction-ℤ x)
    ( sim-reduced-fraction-ℤ x)
```

### The sum of two negative integer fractions is negative

```agda
is-negative-add-fraction-ℤ :
  {x y : fraction-ℤ} →
  is-negative-fraction-ℤ x →
  is-negative-fraction-ℤ y →
  is-negative-fraction-ℤ (add-fraction-ℤ x y)
is-negative-add-fraction-ℤ {x} {y} P Q =
  is-negative-add-ℤ
    ( is-negative-mul-negative-positive-ℤ
      ( P)
      ( is-positive-denominator-fraction-ℤ y))
    ( is-negative-mul-negative-positive-ℤ
      ( Q)
      ( is-positive-denominator-fraction-ℤ x))
```

### The product of two negative integer fractions is positive

```agda
is-positive-mul-negative-fraction-ℤ :
  {x y : fraction-ℤ} →
  is-negative-fraction-ℤ x →
  is-negative-fraction-ℤ y →
  is-positive-fraction-ℤ (mul-fraction-ℤ x y)
is-positive-mul-negative-fraction-ℤ = is-positive-mul-negative-ℤ
```

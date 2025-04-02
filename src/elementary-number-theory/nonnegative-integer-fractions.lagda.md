# Nonnegative integer fractions

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.nonnegative-integer-fractions where
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
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-integers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.dependent-pair-types
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
{{#concept "nonnegative" Disambiguation="integer fraction" Agda=is-nonnegative-fraction-ℤ}}
if its numerator is a
[nonnegative integer](elementary-number-theory.nonnegative-integers.md).

## Definitions

### The property of being a nonnegative integer fraction

```agda
module _
  (x : fraction-ℤ)
  where

  is-nonnegative-fraction-ℤ : UU lzero
  is-nonnegative-fraction-ℤ = is-nonnegative-ℤ (numerator-fraction-ℤ x)

  is-prop-is-nonnegative-fraction-ℤ : is-prop is-nonnegative-fraction-ℤ
  is-prop-is-nonnegative-fraction-ℤ =
    is-prop-is-nonnegative-ℤ (numerator-fraction-ℤ x)
```

## Properties

### An integer fraction similar to a nonnegative integer fraction is nonnegative

```agda
is-nonnegative-sim-fraction-ℤ :
  (x y : fraction-ℤ) (S : sim-fraction-ℤ x y) →
  is-nonnegative-fraction-ℤ x →
  is-nonnegative-fraction-ℤ y
is-nonnegative-sim-fraction-ℤ x y S N =
  is-nonnegative-left-factor-mul-ℤ
    ( tr
      ( is-nonnegative-ℤ)
      ( S)
      ( is-nonnegative-mul-nonnegative-positive-ℤ
        ( N)
        ( is-positive-denominator-fraction-ℤ y)))
    ( is-positive-denominator-fraction-ℤ x)
```

### The reduced fraction of a nonnegative integer fraction is nonnegative

```agda
is-nonnegative-reduce-fraction-ℤ :
  {x : fraction-ℤ} (P : is-nonnegative-fraction-ℤ x) →
  is-nonnegative-fraction-ℤ (reduce-fraction-ℤ x)
is-nonnegative-reduce-fraction-ℤ {x} =
  is-nonnegative-sim-fraction-ℤ
    ( x)
    ( reduce-fraction-ℤ x)
    ( sim-reduced-fraction-ℤ x)
```

### The sum of two nonnegative integer fractions is nonnegative

```agda
is-nonnegative-add-fraction-ℤ :
  {x y : fraction-ℤ} →
  is-nonnegative-fraction-ℤ x →
  is-nonnegative-fraction-ℤ y →
  is-nonnegative-fraction-ℤ (add-fraction-ℤ x y)
is-nonnegative-add-fraction-ℤ {x} {y} P Q =
  is-nonnegative-add-ℤ
    ( is-nonnegative-mul-nonnegative-positive-ℤ
      ( P)
      ( is-positive-denominator-fraction-ℤ y))
    ( is-nonnegative-mul-nonnegative-positive-ℤ
      ( Q)
      ( is-positive-denominator-fraction-ℤ x))
```

### The product of two nonnegative integer fractions is nonnegative

```agda
is-nonnegative-mul-nonnegative-fraction-ℤ :
  {x y : fraction-ℤ} →
  is-nonnegative-fraction-ℤ x →
  is-nonnegative-fraction-ℤ y →
  is-nonnegative-fraction-ℤ (mul-fraction-ℤ x y)
is-nonnegative-mul-nonnegative-fraction-ℤ = is-nonnegative-mul-ℤ
```

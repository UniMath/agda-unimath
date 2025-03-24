# Positive integer fractions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.positive-integer-fractions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions funext univalence truncations
open import elementary-number-theory.addition-positive-and-negative-integers funext univalence truncations
open import elementary-number-theory.integer-fractions funext univalence truncations
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions funext univalence truncations
open import elementary-number-theory.multiplication-positive-and-negative-integers funext univalence truncations
open import elementary-number-theory.positive-integers funext univalence truncations
open import elementary-number-theory.reduced-integer-fractions funext univalence truncations

open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels
```

</details>

## Idea

An [integer fraction](elementary-number-theory.integer-fractions.md) `x` is said
to be
{{#concept "positive" Disambiguation="integer fraction" Agda=is-positive-fraction-ℤ}}
if its numerator is a
[positive integer](elementary-number-theory.positive-integers.md).

## Definitions

### The property of being a positive integer fraction

```agda
module _
  (x : fraction-ℤ)
  where

  is-positive-fraction-ℤ : UU lzero
  is-positive-fraction-ℤ = is-positive-ℤ (numerator-fraction-ℤ x)

  is-prop-is-positive-fraction-ℤ : is-prop is-positive-fraction-ℤ
  is-prop-is-positive-fraction-ℤ =
    is-prop-is-positive-ℤ (numerator-fraction-ℤ x)
```

## Properties

### An integer fraction similar to a positive integer fraction is positive

```agda
is-positive-sim-fraction-ℤ :
  (x y : fraction-ℤ) (S : sim-fraction-ℤ x y) →
  is-positive-fraction-ℤ x →
  is-positive-fraction-ℤ y
is-positive-sim-fraction-ℤ x y S P =
  is-positive-left-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( S)
      ( is-positive-mul-ℤ P (is-positive-denominator-fraction-ℤ y)))
    ( is-positive-denominator-fraction-ℤ x)
```

### The reduced fraction of a positive integer fraction is positive

```agda
is-positive-reduce-fraction-ℤ :
  {x : fraction-ℤ} (P : is-positive-fraction-ℤ x) →
  is-positive-fraction-ℤ (reduce-fraction-ℤ x)
is-positive-reduce-fraction-ℤ {x} =
  is-positive-sim-fraction-ℤ
    ( x)
    ( reduce-fraction-ℤ x)
    ( sim-reduced-fraction-ℤ x)
```

### The sum of two positive integer fractions is positive

```agda
is-positive-add-fraction-ℤ :
  {x y : fraction-ℤ} →
  is-positive-fraction-ℤ x →
  is-positive-fraction-ℤ y →
  is-positive-fraction-ℤ (add-fraction-ℤ x y)
is-positive-add-fraction-ℤ {x} {y} P Q =
  is-positive-add-ℤ
    ( is-positive-mul-ℤ P (is-positive-denominator-fraction-ℤ y))
    ( is-positive-mul-ℤ Q (is-positive-denominator-fraction-ℤ x))
```

### The product of two positive integer fractions is positive

```agda
is-positive-mul-fraction-ℤ :
  {x y : fraction-ℤ} →
  is-positive-fraction-ℤ x →
  is-positive-fraction-ℤ y →
  is-positive-fraction-ℤ (mul-fraction-ℤ x y)
is-positive-mul-fraction-ℤ {x} {y} = is-positive-mul-ℤ
```

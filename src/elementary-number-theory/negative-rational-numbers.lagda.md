# Negative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.negative-integer-fractions
open import elementary-number-theory.negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.nonzero-rational-numbers

open import foundation.coproduct-types
open import foundation.transport-along-identifications
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
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

  is-negative-ℚ : UU lzero
  is-negative-ℚ = is-negative-fraction-ℤ (fraction-ℚ x)

  is-prop-is-negative-ℚ : is-prop is-negative-ℚ
  is-prop-is-negative-ℚ = is-prop-is-negative-fraction-ℤ (fraction-ℚ x)

  is-negative-prop-ℚ : Prop lzero
  pr1 is-negative-prop-ℚ = is-negative-ℚ
  pr2 is-negative-prop-ℚ = is-prop-is-negative-ℚ
```

### The type of negative rational numbers

```agda
negative-ℚ : UU lzero
negative-ℚ = type-subtype is-negative-prop-ℚ

ℚ⁻ : UU lzero
ℚ⁻ = negative-ℚ

module _
  (x : negative-ℚ)
  where

  rational-ℚ⁻ : ℚ
  rational-ℚ⁻ = pr1 x

  fraction-ℚ⁻ : fraction-ℤ
  fraction-ℚ⁻ = fraction-ℚ rational-ℚ⁻

  numerator-ℚ⁻ : ℤ
  numerator-ℚ⁻ = numerator-ℚ rational-ℚ⁻

  denominator-ℚ⁻ : ℤ
  denominator-ℚ⁻ = denominator-ℚ rational-ℚ⁻

  is-negative-rational-ℚ⁻ : is-negative-ℚ rational-ℚ⁻
  is-negative-rational-ℚ⁻ = pr2 x

  is-negative-fraction-ℚ⁻ : is-negative-fraction-ℤ fraction-ℚ⁻
  is-negative-fraction-ℚ⁻ = is-negative-rational-ℚ⁻

  is-negative-numerator-ℚ⁻ : is-negative-ℤ numerator-ℚ⁻
  is-negative-numerator-ℚ⁻ = is-negative-rational-ℚ⁻

  is-positive-denominator-ℚ⁻ : is-positive-ℤ denominator-ℚ⁻
  is-positive-denominator-ℚ⁻ = is-positive-denominator-ℚ rational-ℚ⁻

abstract
  eq-ℚ⁻ : {x y : ℚ⁻} → rational-ℚ⁻ x ＝ rational-ℚ⁻ y → x ＝ y
  eq-ℚ⁻ {x} {y} = eq-type-subtype is-negative-prop-ℚ
```

## Properties

### The negative rational numbers form a set

```agda
is-set-ℚ⁻ : is-set ℚ⁻
is-set-ℚ⁻ = is-set-type-subtype is-negative-prop-ℚ is-set-ℚ
```

### The rational image of a negative integer is negative

```agda
abstract
  is-negative-rational-ℤ :
    (x : ℤ) → is-negative-ℤ x → is-negative-ℚ (rational-ℤ x)
  is-negative-rational-ℤ x P = P

negative-rational-negative-ℤ : negative-ℤ → ℚ⁻
negative-rational-negative-ℤ (z , pos-z) = rational-ℤ z , pos-z
```

### The rational image of a negative integer fraction is negative

```agda
abstract
  is-negative-rational-fraction-ℤ :
    {x : fraction-ℤ} (P : is-negative-fraction-ℤ x) →
    is-negative-ℚ (rational-fraction-ℤ x)
  is-negative-rational-fraction-ℤ = is-negative-reduce-fraction-ℤ
```

### A rational number `x` is negative if and only if its negation is positive

```agda
is-negative-iff-negation-is-positive-ℚ :
  (q : ℚ) → is-negative-ℚ q ↔ is-positive-ℚ (neg-ℚ q)
pr1 (is-negative-iff-negation-is-positive-ℚ q) = is-positive-neg-is-negative-ℤ
pr2 (is-negative-iff-negation-is-positive-ℚ q) neg-is-pos =
  tr
    ( is-negative-ℤ)
    ( neg-neg-ℤ (numerator-ℚ q))
    ( is-negative-neg-is-positive-ℤ neg-is-pos)
```

### A rational number `x` is negative if and only if `x < 0`

```agda
module _
  (x : ℚ)
  where

  abstract
    le-zero-is-negative-ℚ : is-negative-ℚ x → le-ℚ x zero-ℚ
    le-zero-is-negative-ℚ x-is-neg =
      tr
        ( λ y → le-ℚ y zero-ℚ)
        ( neg-neg-ℚ x)
        ( neg-le-ℚ
          ( zero-ℚ)
          ( neg-ℚ x)
          ( le-zero-is-positive-ℚ
            ( neg-ℚ x)
            ( forward-implication
              ( is-negative-iff-negation-is-positive-ℚ x)
              ( x-is-neg))))

    is-negative-le-zero-ℚ : le-ℚ x zero-ℚ → is-negative-ℚ x
    is-negative-le-zero-ℚ x<0 =
      backward-implication
        ( is-negative-iff-negation-is-positive-ℚ x)
        ( is-positive-le-zero-ℚ
          ( neg-ℚ x)
          ( neg-le-ℚ x zero-ℚ x<0))

    is-negative-iff-le-zero-ℚ : is-negative-ℚ x ↔ le-ℚ x zero-ℚ
    is-negative-iff-le-zero-ℚ =
      le-zero-is-negative-ℚ ,
      is-negative-le-zero-ℚ
```

### The difference of a rational number with a greater rational number is negative

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  is-negative-diff-le-ℚ : is-negative-ℚ (x -ℚ y)
  is-negative-diff-le-ℚ =
    backward-implication
      ( is-negative-iff-negation-is-positive-ℚ (x -ℚ y))
      ( inv-tr
        ( is-positive-ℚ)
        ( distributive-neg-diff-ℚ x y)
        ( is-positive-diff-le-ℚ x y H))

  negative-diff-le-ℚ : ℚ⁻
  negative-diff-le-ℚ = x -ℚ y , is-negative-diff-le-ℚ
```

### Negative rational numbers are nonzero

```agda
abstract
  is-nonzero-is-negative-ℚ : {x : ℚ} → is-negative-ℚ x → is-nonzero-ℚ x
  is-nonzero-is-negative-ℚ {x} H =
    is-nonzero-is-nonzero-numerator-ℚ
      ( x)
      ( is-nonzero-is-negative-ℤ {numerator-ℚ x} H)
```

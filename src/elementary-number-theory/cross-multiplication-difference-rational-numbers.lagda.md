# The cross-multiplication difference of two rational numbers

```agda
module elementary-number-theory.cross-multiplication-difference-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.mediant-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
```

</details>

## Idea

The {{#concept "cross-multiplication difference" Agda=cross-mul-diff-ℚ}} of two
[rational numbers](elementary-number-theory.rational-numbers.md) `p` and `q` is
the
[cross-multiplication difference](elementary-number-theory.cross-multiplication-difference-integer-fractions.md)
of their reduced factions `a/b` and `c/d`, the
[difference](elementary-number-theory.difference-integers.md) of the
[products](elementary-number-theory.multiplication-integers.md) of the numerator
of each rational with the denominator of the other: `c * b - a * d`.

## Definitions

### The cross-multiplication difference of two rational numbers

```agda
cross-mul-diff-ℚ : ℚ → ℚ → ℤ
cross-mul-diff-ℚ p q =
  cross-mul-diff-fraction-ℤ
    ( fraction-ℚ p)
    ( fraction-ℚ q)
```

## Properties

### Swapping the arguments switches the sign of the cross-multiplication difference

```agda
abstract
  skew-commutative-cross-mul-diff-ℚ :
    (x y : ℚ) →
    neg-ℤ (cross-mul-diff-ℚ x y) ＝
    cross-mul-diff-ℚ y x
  skew-commutative-cross-mul-diff-ℚ x y =
    skew-commutative-cross-mul-diff-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
```

### The cross-multiplication difference of zero and an rational number is its numerator

```agda
module _
  (x : ℚ)
  where

  abstract
    cross-mul-diff-zero-ℚ : cross-mul-diff-ℚ zero-ℚ x ＝ numerator-ℚ x
    cross-mul-diff-zero-ℚ = cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x)
```

### The cross-multiplication difference of two rational numbers is zero if and only if they are equal

```agda
abstract
  is-zero-cross-mul-diff-eq-ℚ :
    (x y : ℚ) →
    x ＝ y →
    is-zero-ℤ (cross-mul-diff-ℚ x y)
  is-zero-cross-mul-diff-eq-ℚ x .x refl =
    is-zero-cross-mul-diff-sim-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ x)
      ( refl-sim-fraction-ℤ (fraction-ℚ x))

  eq-is-zero-cross-mul-diff-ℚ :
    (x y : ℚ) →
    is-zero-ℤ (cross-mul-diff-ℚ x y) →
    x ＝ y
  eq-is-zero-cross-mul-diff-ℚ x y H =
    binary-tr
      ( Id)
      ( is-retraction-rational-fraction-ℚ x)
      ( is-retraction-rational-fraction-ℚ y)
      ( eq-ℚ-sim-fraction-ℤ
        ( fraction-ℚ x)
        ( fraction-ℚ y)
        ( sim-is-zero-coss-mul-diff-fraction-ℤ
          ( fraction-ℚ x)
          ( fraction-ℚ y)
          ( H)))
```

### The cross-multiplication difference of `p` and `q` with `p ≤ q` is nonnegative

```agda
module _
  (p q : ℚ)
  where

  opaque
    unfolding leq-ℚ-Prop

    is-nonnegative-cross-mul-diff-leq-ℚ :
      leq-ℚ p q → is-nonnegative-ℤ (cross-mul-diff-ℚ p q)
    is-nonnegative-cross-mul-diff-leq-ℚ H = H

    leq-is-nonnegative-cross-mul-diff-ℚ :
      is-nonnegative-ℤ (cross-mul-diff-ℚ p q) → leq-ℚ p q
    leq-is-nonnegative-cross-mul-diff-ℚ H = H
```

### The cross-multiplication difference of `p` and `q` with `p < q` is positive

```agda
module _
  (p q : ℚ)
  where

  opaque
    unfolding le-ℚ-Prop

    is-positive-cross-mul-diff-le-ℚ :
      le-ℚ p q → is-positive-ℤ (cross-mul-diff-ℚ p q)
    is-positive-cross-mul-diff-le-ℚ H = H

    le-is-positive-cross-mul-diff-ℚ :
      is-positive-ℤ (cross-mul-diff-ℚ p q) → le-ℚ p q
    le-is-positive-cross-mul-diff-ℚ H = H
```

## External links

- [Cross-multiplication](https://en.wikipedia.org/wiki/Cross-multiplication) at
  Wikipedia

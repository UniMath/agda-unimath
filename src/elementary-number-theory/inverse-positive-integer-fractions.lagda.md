# Inverse of positive integer fractions

```agda
module elementary-number-theory.inverse-positive-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.reduced-integer-fractions

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

[Positive integer fractions](elementary-number-theory.positive-integer-fractions.md)
have a multiplicative
{{#concept "inverse" Disambiguation="positive integer fraction" Agda=inv-is-positive-fraction-ℤ}}
up to the canonical similarity relation on
[integer fractions](elementary-number-theory.integer-fractions.md).

## Definitions

### The inverse of a positive integer fraction

```agda
module _
  {x : fraction-ℤ} (H : is-positive-fraction-ℤ x)
  where

  inv-is-positive-fraction-ℤ : fraction-ℤ
  pr1 inv-is-positive-fraction-ℤ = denominator-fraction-ℤ x
  pr1 (pr2 inv-is-positive-fraction-ℤ) = numerator-fraction-ℤ x
  pr2 (pr2 inv-is-positive-fraction-ℤ) = H
```

## Properties

### The inverse of a positive reduced integer fraction is reduced

```agda
module _
  (x : fraction-ℤ) (P : is-positive-fraction-ℤ x)
  where

  is-reduced-inv-is-positive-fraction-ℤ :
    is-reduced-fraction-ℤ x →
    is-reduced-fraction-ℤ (inv-is-positive-fraction-ℤ {x} P)
  is-reduced-inv-is-positive-fraction-ℤ =
    tr
      ( is-one-ℤ)
      ( inv
        ( is-commutative-gcd-ℤ
          ( denominator-fraction-ℤ x)
          ( numerator-fraction-ℤ x)))
```

### The multiplication of a positive integer fraction with its inverse is similar to one

```agda
module _
  (x : fraction-ℤ) (P : is-positive-fraction-ℤ x)
  where

  left-inverse-law-mul-is-positive-fraction-ℤ :
    sim-fraction-ℤ
      (mul-fraction-ℤ (inv-is-positive-fraction-ℤ {x} P) x)
      (one-fraction-ℤ)
  left-inverse-law-mul-is-positive-fraction-ℤ =
    ( right-unit-law-mul-ℤ _) ∙
    ( commutative-mul-ℤ
      ( denominator-fraction-ℤ x)
      ( numerator-fraction-ℤ x)) ∙
    ( inv (left-unit-law-mul-ℤ _))

  right-inverse-law-mul-is-positive-fraction-ℤ :
    sim-fraction-ℤ
      (mul-fraction-ℤ x (inv-is-positive-fraction-ℤ {x} P))
      (one-fraction-ℤ)
  right-inverse-law-mul-is-positive-fraction-ℤ =
    ( right-unit-law-mul-ℤ _) ∙
    ( commutative-mul-ℤ
      ( numerator-fraction-ℤ x)
      ( denominator-fraction-ℤ x)) ∙
    ( inv (left-unit-law-mul-ℤ _))
```

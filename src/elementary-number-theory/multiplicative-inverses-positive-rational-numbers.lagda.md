# Multiplicative inverses of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplicative-inverses-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractions
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

[Positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
are [invertible elements](group-theory.invertible-elements-monoids.md) of the
[multiplicative monoid of rational numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md).

## Definitions

### The inverse of a positive rational number

```agda
module _
  {x : ℚ} (P : is-positive-ℚ x)
  where

  inv-is-positive-ℚ : ℚ
  pr1 inv-is-positive-ℚ = inv-is-positive-fraction-ℤ {fraction-ℚ x} P
  pr2 inv-is-positive-ℚ =
    is-reduced-inv-is-positive-fraction-ℤ
      ( fraction-ℚ x)
      ( P)
      ( is-reduced-fraction-ℚ x)
```

## Properties

### Positive rational numbers are invertible

```agda
module _
  (x : ℚ) (P : is-positive-ℚ x)
  where

  abstract
    left-inverse-law-mul-is-positive-ℚ : (inv-is-positive-ℚ {x} P) *ℚ x ＝ one-ℚ
    left-inverse-law-mul-is-positive-ℚ =
      ( eq-ℚ-sim-fraction-ℤ
        ( mul-fraction-ℤ
          ( inv-is-positive-fraction-ℤ {fraction-ℚ x} P)
          ( fraction-ℚ x))
        ( one-fraction-ℤ)
        ( left-inverse-law-mul-is-positive-fraction-ℤ (fraction-ℚ x) P)) ∙
      ( is-retraction-rational-fraction-ℚ one-ℚ)

    right-inverse-law-mul-is-positive-ℚ : x *ℚ (inv-is-positive-ℚ {x} P) ＝ one-ℚ
    right-inverse-law-mul-is-positive-ℚ =
      (commutative-mul-ℚ x _) ∙ (left-inverse-law-mul-is-positive-ℚ)

  is-invertible-is-positive-ℚ :
    Σ ℚ (λ y → (x *ℚ y ＝ one-ℚ) × (y *ℚ x ＝ one-ℚ))
  pr1 is-invertible-is-positive-ℚ = inv-is-positive-ℚ {x} P
  pr1 (pr2 is-invertible-is-positive-ℚ) = right-inverse-law-mul-is-positive-ℚ
  pr2 (pr2 is-invertible-is-positive-ℚ) = left-inverse-law-mul-is-positive-ℚ
```

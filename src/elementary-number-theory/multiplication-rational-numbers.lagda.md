# Multiplication on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

**Multiplication** on the
[rational numbers](elementary-number-theory.rational-numbers.md) is defined by
extending
[multiplication](elementary-number-theory.multiplication-integer-fractions.md)
on [integer fractions](elementary-number-theory.integer-fractions.md) to the
rational numbers.

## Definition

```agda
mul-ℚ : ℚ → ℚ → ℚ
mul-ℚ (x , p) (y , q) = in-fraction-ℤ (mul-fraction-ℤ x y)

infix 30 _*ℚ_
_*ℚ_ = mul-ℚ
```

## Properties

### Unit laws

```agda
left-unit-law-mul-ℚ : (x : ℚ) → one-ℚ *ℚ x ＝ x
left-unit-law-mul-ℚ x =
  ( eq-ℚ-sim-fractions-ℤ
    ( mul-fraction-ℤ one-fraction-ℤ (fraction-ℚ x))
    ( fraction-ℚ x)
    ( left-unit-law-mul-fraction-ℤ (fraction-ℚ x))) ∙
  ( in-fraction-fraction-ℚ x)

right-unit-law-mul-ℚ : (x : ℚ) → x *ℚ one-ℚ ＝ x
right-unit-law-mul-ℚ x =
  ( eq-ℚ-sim-fractions-ℤ
    ( mul-fraction-ℤ (fraction-ℚ x) one-fraction-ℤ)
    ( fraction-ℚ x)
    ( right-unit-law-mul-fraction-ℤ (fraction-ℚ x))) ∙
  ( in-fraction-fraction-ℚ x)
```

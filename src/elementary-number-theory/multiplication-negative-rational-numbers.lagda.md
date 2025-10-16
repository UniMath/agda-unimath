# Multiplication of negative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-integer-fractions
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
```

</details>

## Idea

The product of two
[negative rational numbers](elementary-number-theory.negative-rational-numbers.md)
is their [product](elementary-number-theory.multiplication-rational-numbers.md)
as [rational numbers](elementary-number-theory.rational-numbers.md), and is
[positive](elementary-number-theory.positive-rational-numbers.md).

## Definition

```agda
opaque
  unfolding mul-ℚ rational-fraction-ℤ

  is-positive-mul-negative-ℚ :
    {x y : ℚ} → is-negative-ℚ x → is-negative-ℚ y → is-positive-ℚ (x *ℚ y)
  is-positive-mul-negative-ℚ {x} {y} P Q =
    is-positive-reduce-fraction-ℤ
      ( is-positive-mul-negative-fraction-ℤ
        { fraction-ℚ x}
        { fraction-ℚ y}
        ( is-negative-fraction-ℚ⁻ (x , P))
        ( is-negative-fraction-ℚ⁻ (y , Q)))

mul-ℚ⁻ : ℚ⁻ → ℚ⁻ → ℚ⁺
mul-ℚ⁻ (p , is-neg-p) (q , is-neg-q) =
  (p *ℚ q , is-positive-mul-negative-ℚ is-neg-p is-neg-q)

infixl 40 _*ℚ⁻_
_*ℚ⁻_ : ℚ⁻ → ℚ⁻ → ℚ⁺
_*ℚ⁻_ = mul-ℚ⁻
```

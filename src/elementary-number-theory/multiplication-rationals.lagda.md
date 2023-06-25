# multiplication on the rationals

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-rationals where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

## Definition

```

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
  equational-reasoning
  one-ℚ *ℚ x
  ＝ x
  by eq-ℚ-sim-fractions-ℤ
    ( mul-fraction-ℤ one-fraction-ℤ (fraction-ℚ x) )
    ( fraction-ℚ x)
    ( left-unit-law-mul-fraction-ℤ (fraction-ℚ x))
    ∙ in-fraction-fraction-ℚ x

right-unit-law-mul-ℚ : (x : ℚ) → x *ℚ one-ℚ ＝ x
right-unit-law-mul-ℚ x =
  equational-reasoning
  x *ℚ one-ℚ
  ＝ x
  by eq-ℚ-sim-fractions-ℤ
    ( mul-fraction-ℤ (fraction-ℚ x) one-fraction-ℤ )
    ( fraction-ℚ x)
    ( right-unit-law-mul-fraction-ℤ (fraction-ℚ x))
    ∙ in-fraction-fraction-ℚ x

```

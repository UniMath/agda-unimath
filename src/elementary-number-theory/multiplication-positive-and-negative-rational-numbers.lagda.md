# Multiplication of positive, negative, and nonnegative rational numbers

```agda
module elementary-number-theory.multiplication-positive-and-negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
```

</details>

## Idea

When we have information about the sign of the factors of a
[rational product](elementary-number-theory.multiplication-rational-numbers.md),
we can deduce the sign of their product too.

## Lemmas

### The product of a positive and a negative rational number is negative

```agda
opaque
  unfolding mul-ℚ

  is-negative-mul-positive-negative-ℚ :
    {x y : ℚ} → is-positive-ℚ x → is-negative-ℚ y → is-negative-ℚ (x *ℚ y)
  is-negative-mul-positive-negative-ℚ pos-x neg-y =
    is-negative-rational-fraction-ℤ
      ( is-negative-mul-positive-negative-ℤ
        ( pos-x)
        ( is-negative-fraction-ℚ⁻ (_ , neg-y)))

mul-positive-negative-ℚ : ℚ⁺ → ℚ⁻ → ℚ⁻
mul-positive-negative-ℚ (p , pos-p) (q , neg-q) =
  ( p *ℚ q , is-negative-mul-positive-negative-ℚ pos-p neg-q)
```

### The product of a negative and a positive rational number is negative

```agda
abstract
  is-negative-mul-negative-positive-ℚ :
    {x y : ℚ} → is-negative-ℚ x → is-positive-ℚ y → is-negative-ℚ (x *ℚ y)
  is-negative-mul-negative-positive-ℚ neg-x pos-y =
    tr
      ( is-negative-ℚ)
      ( commutative-mul-ℚ _ _)
      ( is-negative-mul-positive-negative-ℚ pos-y neg-x)

mul-negative-positive-ℚ : ℚ⁻ → ℚ⁺ → ℚ⁻
mul-negative-positive-ℚ (p , neg-p) (q , pos-q) =
  ( p *ℚ q , is-negative-mul-negative-positive-ℚ neg-p pos-q)
```

#### The product of two nonpositive rational numbers is nonnegative

```agda
abstract
  is-nonnegative-mul-nonpositive-ℚ :
    {x y : ℚ} → is-nonpositive-ℚ x → is-nonpositive-ℚ y →
    is-nonnegative-ℚ (x *ℚ y)
  is-nonnegative-mul-nonpositive-ℚ {x} {y} nonpos-x nonpos-y =
    tr
      ( is-nonnegative-ℚ)
      ( negative-law-mul-ℚ x y)
      ( is-nonnegative-mul-ℚ _ _ nonpos-x nonpos-y)
```

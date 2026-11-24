# Rational powers of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.rational-powers-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-binary-functions
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.integer-fraction-powers-positive-real-numbers
open import real-numbers.integer-powers-positive-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-positive-real-numbers
```

</details>

## Idea

Given a [rational number](elementary-number-theory.rational-numbers.md) `p/q`,
the `p/q`th
{{#concept "power" Disambiguation="a positive real number to a rational power" Agda=rational-power-ℝ⁺}}
of a [positive real number](real-numbers.positive-real-numbers.md) `x` is the
`q`th [root](real-numbers.nonzero-roots-positive-real-numbers.md) of the `p`th
[power](real-numbers.integer-powers-positive-real-numbers.md) of `x`. This
definition obeys the standard exponentiation laws.

## Definition

```agda
rational-power-ℝ⁺ : {l : Level} → ℚ → ℝ⁺ l → ℝ⁺ l
rational-power-ℝ⁺ q = int-fraction-power-ℝ⁺ (fraction-ℚ q)
```

## Properties

### `xᵃᵇ = (xᵃ)ᵇ`

```agda
abstract opaque
  unfolding mul-ℚ rational-fraction-ℤ

  rational-power-mul-ℝ⁺ :
    {l : Level} (a b : ℚ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (a *ℚ b) x ＝ rational-power-ℝ⁺ b (rational-power-ℝ⁺ a x)
  rational-power-mul-ℝ⁺ a b x =
    reduce-int-fraction-power-ℝ⁺ _ x ∙ int-fraction-power-mul-ℝ⁺ _ _ x
```

### `xᵃ⁺ᵇ = xᵃxᵇ`

```agda
abstract opaque
  unfolding add-ℚ rational-fraction-ℤ

  rational-power-add-ℝ⁺ :
    {l : Level} (a b : ℚ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (a +ℚ b) x ＝
    rational-power-ℝ⁺ a x *ℝ⁺ rational-power-ℝ⁺ b x
  rational-power-add-ℝ⁺ a b x =
    reduce-int-fraction-power-ℝ⁺ _ x ∙ int-fraction-power-add-ℝ⁺ _ _ x
```

### `x⁰ = 1`

```agda
abstract
  zero-rational-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → rational-power-ℝ⁺ zero-ℚ x ＝ raise-one-ℝ⁺ l
  zero-rational-power-ℝ⁺ = zero-int-fraction-power-ℝ⁺
```

### `x¹ = x`

```agda
abstract
  one-rational-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → rational-power-ℝ⁺ one-ℚ x ＝ x
  one-rational-power-ℝ⁺ = one-int-fraction-power-ℝ⁺
```

### `(xy)ᵖ = xᵖyᵖ`

```agda
abstract
  distributive-rational-power-mul-ℝ⁺ :
    {l1 l2 : Level} (p : ℚ) (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    rational-power-ℝ⁺ p (x *ℝ⁺ y) ＝
    rational-power-ℝ⁺ p x *ℝ⁺ rational-power-ℝ⁺ p y
  distributive-rational-power-mul-ℝ⁺ p =
    distributive-int-fraction-power-mul-ℝ⁺ (fraction-ℚ p)
```

### `1ᵖ = 1`

```agda
abstract
  rational-power-raise-one-ℝ⁺ :
    {l : Level} (p : ℚ) →
    rational-power-ℝ⁺ p (raise-one-ℝ⁺ l) ＝ raise-one-ℝ⁺ l
  rational-power-raise-one-ℝ⁺ p = int-fraction-power-raise-one-ℝ⁺ (fraction-ℚ p)
```

### `xᵖ⁺¹ = xxᵖ = xᵖx`

```agda
abstract
  rational-power-succ-ℝ⁺' :
    {l : Level} (p : ℚ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (succ-ℚ p) x ＝ x *ℝ⁺ rational-power-ℝ⁺ p x
  rational-power-succ-ℝ⁺' p x =
    ( rational-power-add-ℝ⁺ one-ℚ p x) ∙
    ( ap-mul-ℝ⁺ (one-rational-power-ℝ⁺ x) refl)

  rational-power-succ-ℝ⁺ :
    {l : Level} (p : ℚ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (succ-ℚ p) x ＝ rational-power-ℝ⁺ p x *ℝ⁺ x
  rational-power-succ-ℝ⁺ p x =
    rational-power-succ-ℝ⁺' p x ∙ commutative-mul-ℝ⁺ _ _
```

### Rational powers agree with integer powers

```agda
abstract
  rational-int-power-ℝ⁺ :
    {l : Level} (k : ℤ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (rational-ℤ k) x ＝ int-power-ℝ⁺ k x
  rational-int-power-ℝ⁺ = in-int-fraction-power-ℝ⁺
```

### Rational powers agree with natural powers

```agda
abstract
  rational-nat-power-ℝ⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (rational-ℕ n) x ＝ power-ℝ⁺ n x
  rational-nat-power-ℝ⁺ n x =
    rational-int-power-ℝ⁺ (int-ℕ n) x ∙ int-power-int-ℝ⁺ n x
```

### `x⁻¹` is the multiplicative inverse of `x`

```agda
abstract
  neg-one-rational-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → rational-power-ℝ⁺ neg-one-ℚ x ＝ inv-ℝ⁺ x
  neg-one-rational-power-ℝ⁺ x =
    rational-int-power-ℝ⁺ neg-one-ℤ x ∙ int-neg-one-power-ℝ⁺ x
```

### `x⁻ᵖ` is the multiplicative inverse of `xᵖ`

```agda
abstract
  neg-rational-power-ℝ⁺ :
    {l : Level} (p : ℚ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (neg-ℚ p) x ＝ inv-ℝ⁺ (rational-power-ℝ⁺ p x)
  neg-rational-power-ℝ⁺ p x =
    equational-reasoning
      rational-power-ℝ⁺ (neg-ℚ p) x
      ＝ rational-power-ℝ⁺ (p *ℚ neg-one-ℚ) x
        by ap-binary rational-power-ℝ⁺ (inv (right-neg-unit-law-mul-ℚ p)) refl
      ＝ rational-power-ℝ⁺ neg-one-ℚ (rational-power-ℝ⁺ p x)
        by rational-power-mul-ℝ⁺ p neg-one-ℚ x
      ＝ inv-ℝ⁺ (rational-power-ℝ⁺ p x)
        by neg-one-rational-power-ℝ⁺ _
```

# Integer fraction powers of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.rational-powers-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.integer-fraction-powers-positive-real-numbers
open import real-numbers.integer-powers-positive-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.nonzero-natural-roots-positive-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

We define the
{{#concept "power operation" Disambiguation="positive reals to rational powers" Agda=rational-power-ℝ⁺}}
raising [positive real numbers](real-numbers.positive-real-numbers.md) to
[rational](elementary-number-theory.rational-numbers.md) powers in terms of the
corresponding
[operation](real-numbers.integer-fraction-powers-positive-real-numbers.md) on
[integer fractions](elementary-number-theory.integer-fractions.md).

## Definition

```agda
rational-power-ℝ⁺ : {l : Level} → ℚ → ℝ⁺ l → ℝ⁺ l
rational-power-ℝ⁺ q =
  int-fraction-power-ℝ⁺ (fraction-ℚ q)
```

## Properties

### `xᵃ⁺ᵇ = xᵃxᵇ`

```agda
abstract opaque
  unfolding add-ℚ rational-fraction-ℤ

  distributive-power-add-rational-power-ℝ⁺ :
    {l : Level} (p q : ℚ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (p +ℚ q) x ＝
    rational-power-ℝ⁺ p x *ℝ⁺ rational-power-ℝ⁺ q x
  distributive-power-add-rational-power-ℝ⁺ p q x =
    equational-reasoning
      int-fraction-power-ℝ⁺
        ( reduce-fraction-ℤ (fraction-ℚ p +fraction-ℤ fraction-ℚ q))
        ( x)
      ＝ int-fraction-power-ℝ⁺ (fraction-ℚ p +fraction-ℤ fraction-ℚ q) x
        by inv (reduce-int-fraction-power-ℝ⁺ _ x)
      ＝
        ( int-fraction-power-ℝ⁺ (fraction-ℚ p) x) *ℝ⁺
        ( int-fraction-power-ℝ⁺ (fraction-ℚ q) x)
        by distributive-add-integer-fraction-power-ℝ⁺ _ _ x
```

### `xᵃᵇ = (xᵃ)ᵇ`

```agda
abstract opaque
  unfolding mul-ℚ rational-fraction-ℤ

  power-mul-rational-power-ℝ⁺ :
    {l : Level} (p q : ℚ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (p *ℚ q) x ＝ rational-power-ℝ⁺ q (rational-power-ℝ⁺ p x)
  power-mul-rational-power-ℝ⁺ p q x =
    equational-reasoning
      int-fraction-power-ℝ⁺
        ( reduce-fraction-ℤ (fraction-ℚ p *fraction-ℤ fraction-ℚ q))
        ( x)
      ＝ int-fraction-power-ℝ⁺ (fraction-ℚ p *fraction-ℤ fraction-ℚ q) x
        by inv (reduce-int-fraction-power-ℝ⁺ _ x)
      ＝ rational-power-ℝ⁺ q (rational-power-ℝ⁺ p x)
        by mul-int-fraction-power-ℝ⁺ _ _ x
```

### `(xy)ᵃ = xᵃyᵃ`

```agda
abstract
  distributive-rational-power-mul-ℝ⁺ :
    {l1 l2 : Level} (q : ℚ) (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    rational-power-ℝ⁺ q (x *ℝ⁺ y) ＝
    rational-power-ℝ⁺ q x *ℝ⁺ rational-power-ℝ⁺ q y
  distributive-rational-power-mul-ℝ⁺ q =
    distributive-int-fraction-power-mul-ℝ⁺ (fraction-ℚ q)
```

### `x⁻ᵃ` is the multiplicative inverse of `xᵃ`

```agda
abstract opaque
  unfolding neg-ℚ

  neg-rational-power-ℝ⁺ :
    {l : Level} (q : ℚ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (neg-ℚ q) x ＝ inv-ℝ⁺ (rational-power-ℝ⁺ q x)
  neg-rational-power-ℝ⁺ q =
    neg-int-fraction-power-ℝ⁺ (fraction-ℚ q)
```

### The canonical embedding of integers in the rational numbers preserves powers of positive real numbers

```agda
abstract
  rational-ℤ-power-ℝ⁺ :
    {l : Level} (k : ℤ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (rational-ℤ k) x ＝ int-power-ℝ⁺ k x
  rational-ℤ-power-ℝ⁺ = int-fraction-in-fraction-power-ℝ⁺
```

### The canonical embedding of natural numbers in the rational numbers preserves powers of positive real numbers

```agda
abstract
  rational-ℕ-power-ℝ⁺ :
    {l : Level} (n : ℕ) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (rational-ℕ n) x ＝ power-ℝ⁺ n x
  rational-ℕ-power-ℝ⁺ n x =
    rational-ℤ-power-ℝ⁺ (int-ℕ n) x ∙ int-power-int-ℝ⁺ n x
```

### `x¹ = x`

```agda
abstract
  one-ℚ-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → rational-power-ℝ⁺ one-ℚ x ＝ x
  one-ℚ-power-ℝ⁺ x =
    rational-ℕ-power-ℝ⁺ 1 x ∙ eq-ℝ⁺ _ _ (refl {x = real-ℝ⁺ x})
```

### `x⁰ = 1`

```agda
abstract
  zero-ℚ-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → rational-power-ℝ⁺ zero-ℚ x ＝ raise-ℝ⁺ l one-ℝ⁺
  zero-ℚ-power-ℝ⁺ {l} x =
    rational-ℕ-power-ℝ⁺ 0 x ∙ eq-ℝ⁺ _ _ (refl {x = raise-ℝ l one-ℝ})
```

### `x⁻¹` is the multiplicative inverse of `x`

```agda
abstract
  neg-one-ℚ-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → rational-power-ℝ⁺ neg-one-ℚ x ＝ inv-ℝ⁺ x
  neg-one-ℚ-power-ℝ⁺ x =
    rational-ℤ-power-ℝ⁺ neg-one-ℤ x ∙ int-neg-one-power-ℝ⁺ x
```

### `x` to the `1/n` power is the `n`th root of `x`

```agda
abstract opaque
  unfolding is-positive-rational-ℤ inv-ℚ⁺

  reciprocal-rational-ℕ⁺-power-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁺ l) →
    rational-power-ℝ⁺ (reciprocal-rational-ℕ⁺ n) x ＝
    nonzero-nat-root-ℝ⁺ n x
  reciprocal-rational-ℕ⁺-power-ℝ⁺ n x =
    ap-binary
      ( nonzero-nat-root-ℝ⁺)
      ( is-retraction-positive-nat-ℤ⁺ n)
      ( int-one-power-ℝ⁺ x)
```

# Integer fraction powers of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.integer-fraction-powers-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import real-numbers.positive-real-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.integers
open import foundation.action-on-identifications-functions
open import foundation.universe-levels
open import elementary-number-theory.positive-integers
open import foundation.dependent-pair-types
open import foundation.identity-types
open import elementary-number-theory.integer-fractions
open import real-numbers.nonzero-natural-roots-positive-real-numbers
open import real-numbers.integer-powers-positive-real-numbers
```

</details>

## Idea

For any [positive](real-numbers.positive-real-numbers.md)
[real number](real-numbers.dedekind-real-numbers.md) `x` and any
[integer fraction](elementary-number-theory.integer-fractions.md) `p/q`, we can
define the
{{#concept "power operation" Disambiguation="positive real numbers to integer fraction powers" Agda=int-fraction-power-ℝ⁺}}
$x ↦ x^{p/q}$ to map `x` to the `q`th
[root](real-numbers.nonzero-natural-roots-positive-real-numbers.md) of the `p`th
[power](real-numbers.integer-powers-positive-real-numbers.md) of `x`.

## Definition

```agda
int-fraction-power-ℝ⁺ : {l : Level} → fraction-ℤ → ℝ⁺ l → ℝ⁺ l
int-fraction-power-ℝ⁺ (p , q⁺) x =
  nonzero-nat-root-ℝ⁺ (positive-nat-ℤ⁺ q⁺) (int-power-ℝ⁺ p x)
```

## Properties

### The canonical embedding of integers in the integer fractions preserves powers

```agda
abstract
  int-fraction-in-fraction-power-ℝ⁺ :
    {l : Level} (k : ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (in-fraction-ℤ k) x ＝ int-power-ℝ⁺ k x
  int-fraction-in-fraction-power-ℝ⁺ k x =
    equational-reasoning
      nonzero-nat-root-ℝ⁺ (positive-nat-ℤ⁺ one-ℤ⁺) (int-power-ℝ⁺ k x)
      ＝ nonzero-nat-root-ℝ⁺ one-ℕ⁺ (int-power-ℝ⁺ k x)
        by
          ap
            ( λ l → nonzero-nat-root-ℝ⁺ l (int-power-ℝ⁺ k x))
            ( eq-nonzero-ℕ (refl {x = 1}))
      ＝ int-power-ℝ⁺ k x
        by root-one-ℝ⁺ _
```

### `x` to the `kp/kq` power equals x to the `p/q` power

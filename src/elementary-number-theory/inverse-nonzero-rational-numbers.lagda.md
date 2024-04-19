# Inverse of nonzero rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.inverse-nonzero-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inverse-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

[Nonzero rational numbers](elementary-number-theory.nonzero-rational-numbers.md)
have a multiplicative inverse.

## Lemma

### A rational number is invertible if and only if it is nonzero

```agda
module _
  (x : ℚ)
  where

  is-invertible-is-nonzero-ℚ :
    is-nonzero-ℚ x →
    Σ ℚ (λ y → (x *ℚ y ＝ one-ℚ) × (y *ℚ x ＝ one-ℚ))
  is-invertible-is-nonzero-ℚ H =
    rec-coproduct
      ( ( map-Σ _
          ( neg-ℚ)
          ( λ y →
            map-product
              ( swap-neg-mul-ℚ x y ∙_)
              ( inv (swap-neg-mul-ℚ y x) ∙_))) ∘
        ( is-invertible-is-positive-ℚ (neg-ℚ x)))
      ( is-invertible-is-positive-ℚ x)
      ( decide-is-negative-is-positive-is-nonzero-ℚ H)

  is-nonzero-is-invertible-ℚ :
    Σ ℚ (λ y → (x *ℚ y ＝ one-ℚ) × (y *ℚ x ＝ one-ℚ)) →
    is-nonzero-ℚ x
  is-nonzero-is-invertible-ℚ (y , L , _) =
    is-nonzero-left-factor-mul-ℚ x y (inv-tr is-nonzero-ℚ L is-nonzero-one-ℚ)
```

## Definitions

### The inverse of a nonzero rational number

```agda
module _
  {x : ℚ} (H : is-nonzero-ℚ x)
  where

  inv-is-nonzero-ℚ : ℚ
  inv-is-nonzero-ℚ = pr1 (is-invertible-is-nonzero-ℚ x H)
```

## Properties

### Multiplicative inverse laws for nonzero rational numbers

```agda
module _
  (x : ℚ) (H : is-nonzero-ℚ x)
  where

  abstract
    left-inverse-law-mul-is-nonzero-ℚ : (inv-is-nonzero-ℚ H *ℚ x) ＝ one-ℚ
    left-inverse-law-mul-is-nonzero-ℚ =
      pr2 (pr2 (is-invertible-is-nonzero-ℚ x H))

    right-inverse-law-mul-is-nonzero-ℚ : (x *ℚ inv-is-nonzero-ℚ H) ＝ one-ℚ
    right-inverse-law-mul-is-nonzero-ℚ =
      pr1 (pr2 (is-invertible-is-nonzero-ℚ x H))
```

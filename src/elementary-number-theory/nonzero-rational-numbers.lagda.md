# Nonzero rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.nonzero-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The type of
{{#concept "nonzero" Disambiguation="rational number" Agda=nonzero-ℚ}}
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definitions

### The property of being a nonzero rational number

```agda
is-nonzero-prop-ℚ : ℚ → Prop lzero
is-nonzero-prop-ℚ x = (is-nonzero-ℚ x , is-prop-neg)
```

### The nonzero rational numbers

```agda
nonzero-ℚ : UU lzero
nonzero-ℚ = type-subtype is-nonzero-prop-ℚ

module _
  (x : nonzero-ℚ)
  where

  rational-nonzero-ℚ : ℚ
  rational-nonzero-ℚ = pr1 x

  is-nonzero-rational-nonzero-ℚ : is-nonzero-ℚ rational-nonzero-ℚ
  is-nonzero-rational-nonzero-ℚ = pr2 x

abstract
  eq-nonzero-ℚ :
    {x y : nonzero-ℚ} → rational-nonzero-ℚ x ＝ rational-nonzero-ℚ y → x ＝ y
  eq-nonzero-ℚ {x} {y} = eq-type-subtype is-nonzero-prop-ℚ
```

## Properties

### A rational number is nonzero if and only if its numerator is a nonzero integer

```agda
module _
  (x : ℚ)
  where

  abstract
    is-nonzero-numerator-is-nonzero-ℚ :
      is-nonzero-ℚ x → is-nonzero-ℤ (numerator-ℚ x)
    is-nonzero-numerator-is-nonzero-ℚ H =
      H ∘ (is-zero-is-zero-numerator-ℚ x)

    is-nonzero-is-nonzero-numerator-ℚ :
      is-nonzero-ℤ (numerator-ℚ x) → is-nonzero-ℚ x
    is-nonzero-is-nonzero-numerator-ℚ H = H ∘ (ap numerator-ℚ)
```

### one-ℚ is nonzero

```agda
abstract
  is-nonzero-one-ℚ : is-nonzero-ℚ one-ℚ
  is-nonzero-one-ℚ =
    is-nonzero-is-nonzero-numerator-ℚ
      ( one-ℚ)
      ( is-nonzero-one-ℤ)

one-nonzero-ℚ : nonzero-ℚ
one-nonzero-ℚ = (one-ℚ , is-nonzero-one-ℚ)
```

### The negative of a nonzero rational number is nonzero

```agda
abstract
  is-nonzero-neg-ℚ : (x : ℚ) → is-nonzero-ℚ x → is-nonzero-ℚ (neg-ℚ x)
  is-nonzero-neg-ℚ x H =
    is-nonzero-is-nonzero-numerator-ℚ
      ( neg-ℚ x)
      ( is-nonzero-neg-nonzero-ℤ
        ( numerator-ℚ x)
        ( is-nonzero-numerator-is-nonzero-ℚ x H))
```

### The nonzero negative of a nonzero rational number

```agda
neg-nonzero-ℚ : nonzero-ℚ → nonzero-ℚ
neg-nonzero-ℚ (x , H) = (neg-ℚ x , is-nonzero-neg-ℚ x H)
```

### The product of two nonzero rational numbers is nonzero

```agda
abstract
  is-nonzero-mul-ℚ :
    {x y : ℚ} → is-nonzero-ℚ x → is-nonzero-ℚ y → is-nonzero-ℚ (x *ℚ y)
  is-nonzero-mul-ℚ {x} {y} H K =
    rec-coproduct H K ∘ (decide-is-zero-factor-is-zero-mul-ℚ x y)
```

### The nonzero product of two nonzero rational numbers

```agda
mul-nonzero-ℚ : nonzero-ℚ → nonzero-ℚ → nonzero-ℚ
mul-nonzero-ℚ (x , P) (y , Q) = (x *ℚ y , is-nonzero-mul-ℚ P Q)
```

### Unit laws for multiplication of nonzero rational numbers

```agda
module _
  (x : nonzero-ℚ)
  where

  abstract
    left-unit-law-mul-nonzero-ℚ : mul-nonzero-ℚ one-nonzero-ℚ x ＝ x
    left-unit-law-mul-nonzero-ℚ =
      eq-nonzero-ℚ (left-unit-law-mul-ℚ (rational-nonzero-ℚ x))

    right-unit-law-mul-nonzero-ℚ : mul-nonzero-ℚ x one-nonzero-ℚ ＝ x
    right-unit-law-mul-nonzero-ℚ =
      eq-nonzero-ℚ (right-unit-law-mul-ℚ (rational-nonzero-ℚ x))
```

### The factors of a nonzero product of rational numbers are nonzero

```agda
abstract
  is-nonzero-left-factor-mul-ℚ :
    (x y : ℚ) → is-nonzero-ℚ (x *ℚ y) → is-nonzero-ℚ x
  is-nonzero-left-factor-mul-ℚ x y H Z =
    H (ap (_*ℚ y) Z ∙ left-zero-law-mul-ℚ y)

  is-nonzero-right-factor-mul-ℚ :
    (x y : ℚ) → is-nonzero-ℚ (x *ℚ y) → is-nonzero-ℚ y
  is-nonzero-right-factor-mul-ℚ x y H Z =
    H (ap (x *ℚ_) Z ∙ right-zero-law-mul-ℚ x)
```

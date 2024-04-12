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

ℚˣ : UU lzero
ℚˣ = nonzero-ℚ

module _
  (x : nonzero-ℚ)
  where

  rational-ℚˣ : ℚ
  rational-ℚˣ = pr1 x

  is-nonzero-rational-ℚˣ : is-nonzero-ℚ rational-ℚˣ
  is-nonzero-rational-ℚˣ = pr2 x

abstract
  eq-ℚˣ : {x y : ℚˣ} → rational-ℚˣ x ＝ rational-ℚˣ y → x ＝ y
  eq-ℚˣ {x} {y} = eq-type-subtype is-nonzero-prop-ℚ
```

## Properties

### A rational number is nonzero if and only if its numerator is a nonzero integer

```agda
module _
  (x : ℚ)
  where

  is-nonzero-numerator-is-nonzero-ℚ :
    is-nonzero-ℚ x → is-nonzero-ℤ (numerator-ℚ x)
  is-nonzero-numerator-is-nonzero-ℚ H K =
    H
      ( ( inv (is-retraction-rational-fraction-ℚ x)) ∙
        ( eq-ℚ-sim-fraction-ℤ
          ( fraction-ℚ x)
          ( fraction-ℚ zero-ℚ)
          ( eq-is-zero-ℤ
            ( ap (mul-ℤ' one-ℤ) K ∙ right-zero-law-mul-ℤ one-ℤ)
            ( left-zero-law-mul-ℤ (denominator-ℚ x))) ∙
        ( is-retraction-rational-fraction-ℚ zero-ℚ)))

  is-nonzero-is-nonzero-numerator-ℚ :
    is-nonzero-ℤ (numerator-ℚ x) → is-nonzero-ℚ x
  is-nonzero-is-nonzero-numerator-ℚ H K = H (ap numerator-ℚ K)
```

### one-ℚ is nonzero

```agda
is-nonzero-one-ℚ : is-nonzero-ℚ one-ℚ
is-nonzero-one-ℚ =
  is-nonzero-is-nonzero-numerator-ℚ
    ( one-ℚ)
    ( is-nonzero-one-ℤ)

one-ℚˣ : nonzero-ℚ
one-ℚˣ = (one-ℚ , is-nonzero-one-ℚ)
```

### The negative of a nonzero rational number is nonzero

```agda
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
neg-ℚˣ : ℚˣ → ℚˣ
neg-ℚˣ (x , H) = (neg-ℚ x , is-nonzero-neg-ℚ x H)
```

### The product of two nonzero rational numbers is nonzero

```agda
is-nonzero-mul-ℚ :
  {x y : ℚ} → is-nonzero-ℚ x → is-nonzero-ℚ y → is-nonzero-ℚ (x *ℚ y)
is-nonzero-mul-ℚ {x} {y} H K =
  rec-coproduct H K ∘ (decide-is-zero-factor-is-zero-mul-ℚ x y)
```

### The nonzero product of two nonzero rational numbers

```agda
mul-ℚˣ : ℚˣ → ℚˣ → ℚˣ
mul-ℚˣ (x , P) (y , Q) = (x *ℚ y , is-nonzero-mul-ℚ P Q)

infixl 40 _*ℚˣ_
_*ℚˣ_ = mul-ℚˣ
```

### Unit laws for multiplication of nonzero rational numbers

```agda
module _
  (x : ℚˣ)
  where

  abstract
    left-unit-law-mul-ℚˣ : one-ℚˣ *ℚˣ x ＝ x
    left-unit-law-mul-ℚˣ = eq-ℚˣ (left-unit-law-mul-ℚ (rational-ℚˣ x))

    right-unit-law-mul-ℚˣ : x *ℚˣ one-ℚˣ ＝ x
    right-unit-law-mul-ℚˣ = eq-ℚˣ (right-unit-law-mul-ℚ (rational-ℚˣ x))
```

### The factors of a nonzero product of rational numbers are nonzero

```agda
is-nonzero-left-factor-mul-ℚ :
  (x y : ℚ) → is-nonzero-ℚ (x *ℚ y) → is-nonzero-ℚ x
is-nonzero-left-factor-mul-ℚ x y H Z =
  H (ap (_*ℚ y) Z ∙ left-zero-law-mul-ℚ y)

is-nonzero-right-factor-mul-ℚ :
  (x y : ℚ) → is-nonzero-ℚ (x *ℚ y) → is-nonzero-ℚ y
is-nonzero-right-factor-mul-ℚ x y H Z =
  H (ap (x *ℚ_) Z ∙ right-zero-law-mul-ℚ x)
```

# Multiplicative inverses of negative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplicative-inverses-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

If a [real number](real-numbers.dedekind-real-numbers.md) `x` is
[negative](real-numbers.negative-real-numbers.md), then it has a
{{#concept "multiplicative inverse" Disambiguation="negative real numbers" Agda=inv-ℝ⁻}},
a unique, negative real number `y` such that the
[product](real-numbers.multiplication-real-numbers.md) of `x` and `y` is 1.

## Definition

```agda
inv-ℝ⁻ : {l : Level} → ℝ⁻ l → ℝ⁻ l
inv-ℝ⁻ x = neg-ℝ⁺ (inv-ℝ⁺ (neg-ℝ⁻ x))

real-inv-ℝ⁻ : {l : Level} → ℝ⁻ l → ℝ l
real-inv-ℝ⁻ x = real-ℝ⁻ (inv-ℝ⁻ x)
```

## Properties

### The multiplicative inverse is a multiplicative inverse

```agda
abstract
  left-inverse-law-mul-ℝ⁻ :
    {l : Level} → (x : ℝ⁻ l) → sim-ℝ (real-inv-ℝ⁻ x *ℝ real-ℝ⁻ x) one-ℝ
  left-inverse-law-mul-ℝ⁻ x⁻@(x , _) =
    inv-tr
      ( λ y → sim-ℝ y one-ℝ)
      ( left-negative-law-mul-ℝ _ _ ∙ inv (right-negative-law-mul-ℝ _ _))
      ( left-inverse-law-mul-ℝ⁺ (neg-ℝ⁻ x⁻))

  right-inverse-law-mul-ℝ⁻ :
    {l : Level} → (x : ℝ⁻ l) → sim-ℝ (real-ℝ⁻ x *ℝ real-inv-ℝ⁻ x) one-ℝ
  right-inverse-law-mul-ℝ⁻ x =
    tr
      ( λ y → sim-ℝ y one-ℝ)
      ( commutative-mul-ℝ _ _)
      ( left-inverse-law-mul-ℝ⁻ x)
```

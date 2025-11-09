# Magnitude of complex numbers

```agda
{-# OPTIONS --lossy-unification #-}

module complex-numbers.magnitude-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.multiplication-complex-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
-- sopen import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

The
{{#concept "magnitude" WD="magnitude of a complex number" WDID=Q3317982 Agda=magnitude-ℂ}}
of a [complex number](complex-numbers.complex-numbers.md) `a + bi` is defined as
$$\sqrt{a^2 + b^2}}$$.

## Definition

```agda
nonnegative-squared-magnitude-ℂ : {l : Level} → ℂ l → ℝ⁰⁺ l
nonnegative-squared-magnitude-ℂ (a +iℂ b) =
  nonnegative-square-ℝ a +ℝ⁰⁺ nonnegative-square-ℝ b

squared-magnitude-ℂ : {l : Level} → ℂ l → ℝ l
squared-magnitude-ℂ z = real-ℝ⁰⁺ (nonnegative-squared-magnitude-ℂ z)

∥_∥²ℂ : {l : Level} → ℂ l → ℝ l
∥ z ∥²ℂ = squared-magnitude-ℂ z

nonnegative-magnitude-ℂ : {l : Level} → ℂ l → ℝ⁰⁺ l
nonnegative-magnitude-ℂ z = sqrt-ℝ⁰⁺ (nonnegative-squared-magnitude-ℂ z)

magnitude-ℂ : {l : Level} → ℂ l → ℝ l
magnitude-ℂ z = real-ℝ⁰⁺ (nonnegative-magnitude-ℂ z)

∥_∥ℂ : {l : Level} → ℂ l → ℝ l
∥ z ∥ℂ = magnitude-ℂ z
```

## Properties

### The square of the magnitude of `z` is the product of `z` and the conjugate of `z`

```agda
abstract
  eq-squared-magnitude-mul-conjugate-ℂ :
    {l : Level} (z : ℂ l) →
    z *ℂ conjugate-ℂ z ＝ complex-ℝ (squared-magnitude-ℂ z)
  eq-squared-magnitude-mul-conjugate-ℂ (a +iℂ b) =
    eq-ℂ
      ( equational-reasoning
        square-ℝ a -ℝ (b *ℝ neg-ℝ b)
        ＝ square-ℝ a -ℝ (neg-ℝ (square-ℝ b))
          by ap-diff-ℝ refl (right-negative-law-mul-ℝ _ _)
        ＝ square-ℝ a +ℝ square-ℝ b
          by ap-add-ℝ refl (neg-neg-ℝ _))
      ( eq-sim-ℝ
        ( similarity-reasoning-ℝ
          a *ℝ neg-ℝ b +ℝ b *ℝ a
          ~ℝ neg-ℝ (a *ℝ b) +ℝ a *ℝ b
            by
              sim-eq-ℝ
                ( ap-add-ℝ
                  ( right-negative-law-mul-ℝ a b)
                  ( commutative-mul-ℝ b a))
          ~ℝ zero-ℝ
            by left-inverse-law-add-ℝ (a *ℝ b)
          ~ℝ raise-ℝ _ zero-ℝ
            by sim-raise-ℝ _ _))
```

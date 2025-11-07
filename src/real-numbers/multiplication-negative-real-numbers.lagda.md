# Multiplication of negative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of pairs of positive real numbers" Agda=mul-ℝ⁻}}
of two [negative](real-numbers.negative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) is their
[product](real-numbers.multiplication-real-numbers.md) as real numbers, and is
[positive](real-numbers.positive-real-numbers.md).

## Definition

```agda
abstract
  is-positive-mul-is-negative-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    is-negative-ℝ x → is-negative-ℝ y → is-positive-ℝ (x *ℝ y)
  is-positive-mul-is-negative-ℝ {x = x} {y = y} is-neg-x is-neg-y =
    tr
      ( is-positive-ℝ)
      ( negative-law-mul-ℝ x y)
      ( is-positive-mul-ℝ
        ( neg-is-negative-ℝ x is-neg-x)
        ( neg-is-negative-ℝ y is-neg-y))

mul-ℝ⁻ : {l1 l2 : Level} → ℝ⁻ l1 → ℝ⁻ l2 → ℝ⁺ (l1 ⊔ l2)
mul-ℝ⁻ (x , is-neg-x) (y , is-neg-y) =
  (x *ℝ y , is-positive-mul-is-negative-ℝ is-neg-x is-neg-y)

infixl 40 _*ℝ⁻_
_*ℝ⁻_ : {l1 l2 : Level} → ℝ⁻ l1 → ℝ⁻ l2 → ℝ⁺ (l1 ⊔ l2)
_*ℝ⁻_ = mul-ℝ⁻
```

## Properties

### Multiplication by a negative real number reverses strict inequality

```agda
abstract
  reverses-le-left-mul-ℝ⁻ :
    {l1 l2 l3 : Level} (x : ℝ⁻ l1) (y : ℝ l2) (z : ℝ l3) → le-ℝ y z →
    le-ℝ (real-ℝ⁻ x *ℝ z) (real-ℝ⁻ x *ℝ y)
  reverses-le-left-mul-ℝ⁻ x y z y<z =
    binary-tr
      ( le-ℝ)
      ( ap neg-ℝ (left-negative-law-mul-ℝ _ _) ∙ neg-neg-ℝ _)
      ( ap neg-ℝ (left-negative-law-mul-ℝ _ _) ∙ neg-neg-ℝ _)
      ( neg-le-ℝ (preserves-le-left-mul-ℝ⁺ (neg-ℝ⁻ x) y z y<z))
```

### Multiplication by a negative real number reverses inequality

```agda
abstract
  reverses-leq-left-mul-ℝ⁻ :
    {l1 l2 l3 : Level} (x : ℝ⁻ l1) (y : ℝ l2) (z : ℝ l3) → leq-ℝ y z →
    leq-ℝ (real-ℝ⁻ x *ℝ z) (real-ℝ⁻ x *ℝ y)
  reverses-leq-left-mul-ℝ⁻ x y z y<z =
    binary-tr
      ( leq-ℝ)
      ( ap neg-ℝ (left-negative-law-mul-ℝ _ _) ∙ neg-neg-ℝ _)
      ( ap neg-ℝ (left-negative-law-mul-ℝ _ _) ∙ neg-neg-ℝ _)
      ( neg-leq-ℝ (preserves-leq-left-mul-ℝ⁺ (neg-ℝ⁻ x) y z y<z))
```

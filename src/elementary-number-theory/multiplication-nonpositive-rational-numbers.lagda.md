# Multiplication by nonpositive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-nonpositive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The product of two
[nonpositive rational numbers](elementary-number-theory.nonpositive-rational-numbers.md)
is their [product](elementary-number-theory.multiplication-rational-numbers.md)
as [rational numbers](elementary-number-theory.rational-numbers.md), and is
[nonnegative](elementary-number-theory.nonnegative-rational-numbers.md).

## Definition

```agda
opaque
  unfolding is-nonpositive-ℚ

  is-nonnegative-mul-nonpositive-ℚ :
    {x y : ℚ} → is-nonpositive-ℚ x → is-nonpositive-ℚ y →
    is-nonnegative-ℚ (x *ℚ y)
  is-nonnegative-mul-nonpositive-ℚ {x} {y} nonpos-x nonpos-y =
    tr
      ( is-nonnegative-ℚ)
      ( negative-law-mul-ℚ x y)
      ( is-nonnegative-mul-ℚ nonpos-x nonpos-y)

mul-nonpositive-ℚ : ℚ⁰⁻ → ℚ⁰⁻ → ℚ⁰⁺
mul-nonpositive-ℚ (p , nonpos-p) (q , nonpos-q) =
  (p *ℚ q , is-nonnegative-mul-nonpositive-ℚ nonpos-p nonpos-q)
```

## Properties

### Multiplication by a nonpositive rational number reverses inequality

```agda
opaque
  unfolding is-nonpositive-ℚ

  reverses-leq-right-mul-ℚ⁰⁻ :
    (p : ℚ⁰⁻) (q r : ℚ) → leq-ℚ q r →
    leq-ℚ (r *ℚ rational-ℚ⁰⁻ p) (q *ℚ rational-ℚ⁰⁻ p)
  reverses-leq-right-mul-ℚ⁰⁻ (p , nonpos-p) q r q≤r =
    binary-tr
      ( leq-ℚ)
      ( ap neg-ℚ (right-negative-law-mul-ℚ r p) ∙ neg-neg-ℚ _)
      ( ap neg-ℚ (right-negative-law-mul-ℚ q p) ∙ neg-neg-ℚ _)
      ( neg-leq-ℚ
        ( preserves-leq-right-mul-ℚ⁰⁺ (neg-ℚ p , nonpos-p) q r q≤r))
```

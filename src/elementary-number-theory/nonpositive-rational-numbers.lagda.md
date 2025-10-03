# The nonpositive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.nonpositive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A [rational number](elementary-number-theory.rational-numbers.md) `x` is said to
be
{{#concept "nonpositive" Disambiguation="rational number" Agda=is-nonpositive-ℚ}}
if its numerator is a
[nonpositive integer](elementary-number-theory.nonpositive-integers.md).

## Definitions

### The property of being a nonpositive rational number

```agda
module _
  (q : ℚ)
  where

  is-nonpositive-ℚ : UU lzero
  is-nonpositive-ℚ = is-nonnegative-ℚ (neg-ℚ q)

  abstract
    is-prop-is-nonpositive-ℚ : is-prop is-nonpositive-ℚ
    is-prop-is-nonpositive-ℚ = is-prop-is-nonnegative-ℚ (neg-ℚ q)

  is-nonpositive-prop-ℚ : Prop lzero
  is-nonpositive-prop-ℚ = (is-nonpositive-ℚ , is-prop-is-nonpositive-ℚ)
```

### The type of nonpositive rational numbers

```agda
nonpositive-ℚ : UU lzero
nonpositive-ℚ = type-subtype is-nonpositive-prop-ℚ

ℚ⁰⁻ : UU lzero
ℚ⁰⁻ = nonpositive-ℚ

module _
  (x : nonpositive-ℚ)
  where

  rational-ℚ⁰⁻ : ℚ
  rational-ℚ⁰⁻ = pr1 x

  fraction-ℚ⁰⁻ : fraction-ℤ
  fraction-ℚ⁰⁻ = fraction-ℚ rational-ℚ⁰⁻

  numerator-ℚ⁰⁻ : ℤ
  numerator-ℚ⁰⁻ = numerator-ℚ rational-ℚ⁰⁻

  denominator-ℚ⁰⁻ : ℤ
  denominator-ℚ⁰⁻ = denominator-ℚ rational-ℚ⁰⁻
```

## Properties

### Equality on nonpositive rational numbers

```agda
abstract
  eq-ℚ⁰⁻ : {x y : ℚ⁰⁻} → rational-ℚ⁰⁻ x ＝ rational-ℚ⁰⁻ y → x ＝ y
  eq-ℚ⁰⁻ {x} {y} = eq-type-subtype is-nonpositive-prop-ℚ
```

### A rational number is nonpositive if and only if it is less than or equal to zero

```agda
module _
  (q : ℚ)
  where

  opaque
    unfolding neg-ℚ

    leq-zero-is-nonpositive-ℚ : is-nonpositive-ℚ q → leq-ℚ q zero-ℚ
    leq-zero-is-nonpositive-ℚ is-nonpos-q =
      tr
        ( λ p → leq-ℚ p zero-ℚ)
        ( neg-neg-ℚ q)
        ( neg-leq-ℚ _ _ (leq-zero-is-nonnegative-ℚ (neg-ℚ q) is-nonpos-q))

    is-nonpositive-leq-zero-ℚ : leq-ℚ q zero-ℚ → is-nonpositive-ℚ q
    is-nonpositive-leq-zero-ℚ q≤0 =
      is-nonnegative-leq-zero-ℚ (neg-ℚ q) (neg-leq-ℚ _ _ q≤0)

    is-nonpositive-iff-leq-zero-ℚ : is-nonpositive-ℚ q ↔ leq-ℚ q zero-ℚ
    is-nonpositive-iff-leq-zero-ℚ =
      ( leq-zero-is-nonpositive-ℚ ,
        is-nonpositive-leq-zero-ℚ)
```

### If `p < q` and `q` is nonpositive, then `p` is negative

```agda
abstract
  is-negative-le-nonpositive-ℚ :
    (q : ℚ⁰⁻) (p : ℚ) → le-ℚ p (rational-ℚ⁰⁻ q) → is-negative-ℚ p
  is-negative-le-nonpositive-ℚ (q , nonpos-q) p p<q =
    is-negative-le-zero-ℚ
      ( p)
      ( concatenate-le-leq-ℚ p q zero-ℚ
        ( p<q)
        ( leq-zero-is-nonpositive-ℚ q nonpos-q))
```

### Multiplication by a nonpositive rational number reverses inequality

```agda
abstract
  reverses-leq-right-mul-ℚ⁰⁻ :
    (p : ℚ⁰⁻) (q r : ℚ) → leq-ℚ q r →
    leq-ℚ (r *ℚ rational-ℚ⁰⁻ p) (q *ℚ rational-ℚ⁰⁻ p)
  reverses-leq-right-mul-ℚ⁰⁻ (p , nonpos-p) q r q≤r =
    binary-tr
      ( leq-ℚ)
      ( ap neg-ℚ (right-negative-law-mul-ℚ r p) ∙ neg-neg-ℚ _)
      ( ap neg-ℚ (right-negative-law-mul-ℚ q p) ∙ neg-neg-ℚ _)
      ( neg-leq-ℚ _ _
        ( preserves-leq-right-mul-ℚ⁰⁺ (neg-ℚ p , nonpos-p) q r q≤r))
```

# Saturation of inequality of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.saturation-inequality-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.saturation-inequality-real-numbers
open import real-numbers.similarity-nonnegative-real-numbers
```

</details>

## Idea

If `x ≤ y + ε` for [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) `x` and `y` and every
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
then `x ≤ y`.

Despite being a property of
[inequality of nonnegative real numbers](real-numbers.inequality-nonnegative-real-numbers.md),
this is much easier to prove via
[strict inequality](real-numbers.strict-inequality-nonnegative-real-numbers.md),
so this page is dedicated to just this property to prevent circular dependency.

## Definition

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  abstract
    saturated-leq-ℝ⁰⁺ :
      ((ε : ℚ⁺) → leq-ℝ⁰⁺ x (y +ℝ⁰⁺ nonnegative-real-ℚ⁺ ε)) →
      leq-ℝ⁰⁺ x y
    saturated-leq-ℝ⁰⁺ = saturated-leq-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)
```

## Corollaries

### If a nonnegative real number is less than or equal to all positive rational numbers, it is similar to zero

```agda
abstract
  sim-zero-leq-positive-rational-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) →
    ((ε : ℚ⁺) → leq-ℝ⁰⁺ x (nonnegative-real-ℚ⁺ ε)) →
    sim-zero-ℝ⁰⁺ x
  sim-zero-leq-positive-rational-ℝ⁰⁺ x H =
    sim-sim-leq-ℝ
      ( leq-zero-ℝ⁰⁺ x ,
        saturated-leq-ℝ⁰⁺
          ( x)
          ( zero-ℝ⁰⁺)
          ( λ ε → inv-tr (leq-ℝ⁰⁺ x) (left-unit-law-add-ℝ⁰⁺ _) (H ε)))
```

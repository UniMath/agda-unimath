# Addition of positive, negative, and nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-positive-and-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
```

</details>

## Idea

This file describes properties of
[addition](real-numbers.addition-real-numbers.md) of
[positive](real-numbers.positive-real-numbers.md),
[negative](real-numbers.negative-real-numbers.md), and
[nonnegative](real-numbers.nonnegative-real-numbers.md) real numbers.

## Properties

### The sum of a nonnegative and a positive real number is positive

```agda
abstract
  is-positive-add-nonnegative-positive-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    is-nonnegative-ℝ x → is-positive-ℝ y →
    is-positive-ℝ (x +ℝ y)
  is-positive-add-nonnegative-positive-ℝ {x = x} {y = y} 0≤x 0<y =
    is-positive-le-ℝ⁰⁺
      ( x , 0≤x)
      ( x +ℝ y)
      ( le-left-add-real-ℝ⁺ x (y , 0<y))

add-nonnegative-positive-ℝ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁺ l2 → ℝ⁺ (l1 ⊔ l2)
add-nonnegative-positive-ℝ (x , 0≤x) (y , 0<y) =
  ( x +ℝ y , is-positive-add-nonnegative-positive-ℝ 0≤x 0<y)
```

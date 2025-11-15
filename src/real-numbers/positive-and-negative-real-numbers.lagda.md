# Positive and negative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.positive-and-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

On this page, we outline basic relations between
[negative](real-numbers.negative-real-numbers.md),
[nonnegative](real-numbers.nonnegative-real-numbers.md), and
[positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md).

## Properties

### Positive real numbers are nonnegative

```agda
abstract
  is-nonnegative-is-positive-ℝ :
    {l : Level} {x : ℝ l} → is-positive-ℝ x → is-nonnegative-ℝ x
  is-nonnegative-is-positive-ℝ = leq-le-ℝ

nonnegative-ℝ⁺ : {l : Level} → ℝ⁺ l → ℝ⁰⁺ l
nonnegative-ℝ⁺ (x , is-pos-x) = (x , is-nonnegative-is-positive-ℝ is-pos-x)
```

### The negation of a positive real number is negative

```agda
abstract
  neg-is-positive-ℝ :
    {l : Level} (x : ℝ l) → is-positive-ℝ x → is-negative-ℝ (neg-ℝ x)
  neg-is-positive-ℝ x 0<x =
    tr
      ( le-ℝ (neg-ℝ x))
      ( neg-zero-ℝ)
      ( neg-le-ℝ 0<x)

neg-ℝ⁺ : {l : Level} → ℝ⁺ l → ℝ⁻ l
neg-ℝ⁺ (x , is-pos-x) = (neg-ℝ x , neg-is-positive-ℝ x is-pos-x)
```

### The negation of a negative real number is positive

```agda
abstract
  neg-is-negative-ℝ :
    {l : Level} (x : ℝ l) → is-negative-ℝ x → is-positive-ℝ (neg-ℝ x)
  neg-is-negative-ℝ x x<0 =
    tr
      ( λ z → le-ℝ z (neg-ℝ x))
      ( neg-zero-ℝ)
      ( neg-le-ℝ x<0)

neg-ℝ⁻ : {l : Level} → ℝ⁻ l → ℝ⁺ l
neg-ℝ⁻ (x , is-neg-x) = (neg-ℝ x , neg-is-negative-ℝ x is-neg-x)
```

### A real number is negative if and only if its negation is positive

```agda
abstract
  is-negative-is-positive-neg-ℝ :
    {l : Level} (x : ℝ l) → is-positive-ℝ (neg-ℝ x) → is-negative-ℝ x
  is-negative-is-positive-neg-ℝ x 0<-x =
    tr is-negative-ℝ (neg-neg-ℝ x) (neg-is-positive-ℝ (neg-ℝ x) 0<-x)

is-negative-iff-neg-is-positive-ℝ :
  {l : Level} (x : ℝ l) → is-negative-ℝ x ↔ is-positive-ℝ (neg-ℝ x)
is-negative-iff-neg-is-positive-ℝ x =
  ( neg-is-negative-ℝ x ,
    is-negative-is-positive-neg-ℝ x)
```

### A real number is positive if and only if its negation is negative

```agda
abstract
  is-positive-is-negative-neg-ℝ :
    {l : Level} (x : ℝ l) → is-negative-ℝ (neg-ℝ x) → is-positive-ℝ x
  is-positive-is-negative-neg-ℝ x -x<0 =
    tr is-positive-ℝ (neg-neg-ℝ x) (neg-is-negative-ℝ (neg-ℝ x) -x<0)

is-positive-iff-neg-is-negative-ℝ :
  {l : Level} (x : ℝ l) → is-positive-ℝ x ↔ is-negative-ℝ (neg-ℝ x)
is-positive-iff-neg-is-negative-ℝ x =
  ( neg-is-positive-ℝ x ,
    is-positive-is-negative-neg-ℝ x)
```

### If a nonnegative real number `x` is less than a real number `y`, `y` is positive

```agda
abstract
  is-positive-le-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ l2) → le-ℝ (real-ℝ⁰⁺ x) y →
    is-positive-ℝ y
  is-positive-le-ℝ⁰⁺ (x , 0≤x) y = concatenate-leq-le-ℝ zero-ℝ x y 0≤x
```

### Real numbers are not both negative and nonnegative

```agda
abstract
  is-not-negative-and-nonnegative-ℝ :
    {l : Level} {x : ℝ l} → ¬ (is-negative-ℝ x × is-nonnegative-ℝ x)
  is-not-negative-and-nonnegative-ℝ {x = x} (x<0 , 0≤x) =
    not-leq-le-ℝ x zero-ℝ x<0 0≤x
```

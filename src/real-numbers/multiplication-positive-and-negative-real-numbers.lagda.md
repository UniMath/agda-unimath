# Multiplication by positive, negative, and nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-positive-and-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-nonnegative-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

When we have information about the sign of the factors of a
[product](real-numbers.multiplication-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md), we can deduce the sign of
their product too.

## Lemmas

### The product of a positive and a negative real number is negative

```agda
abstract
  is-negative-mul-positive-negative-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-positive-ℝ x → is-negative-ℝ y →
    is-negative-ℝ (x *ℝ y)
  is-negative-mul-positive-negative-ℝ {x = x} {y = y} is-pos-x is-neg-y =
    preserves-le-right-sim-ℝ
      ( x *ℝ y)
      ( x *ℝ zero-ℝ)
      ( zero-ℝ)
      ( right-zero-law-mul-ℝ x)
      ( preserves-le-left-mul-ℝ⁺ (x , is-pos-x) is-neg-y)

mul-positive-negative-ℝ :
  {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁻ l2 → ℝ⁻ (l1 ⊔ l2)
mul-positive-negative-ℝ (x , is-pos-x) (y , is-neg-y) =
  ( x *ℝ y , is-negative-mul-positive-negative-ℝ is-pos-x is-neg-y)
```

### The product of a negative and a positive real number is negative

```agda
abstract
  is-negative-mul-negative-positive-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-negative-ℝ x → is-positive-ℝ y →
    is-negative-ℝ (x *ℝ y)
  is-negative-mul-negative-positive-ℝ {x = x} {y = y} x<0 0<y =
    tr
      ( is-negative-ℝ)
      ( commutative-mul-ℝ y x)
      ( is-negative-mul-positive-negative-ℝ 0<y x<0)

mul-negative-positive-ℝ :
  {l1 l2 : Level} → ℝ⁻ l1 → ℝ⁺ l2 → ℝ⁻ (l1 ⊔ l2)
mul-negative-positive-ℝ (x , is-neg-x) (y , is-pos-y) =
  ( x *ℝ y , is-negative-mul-negative-positive-ℝ is-neg-x is-pos-y)
```

### If `x` is positive and `xy` is nonnegative, `y` is nonnegative

```agda
abstract
  is-nonnegative-is-nonnegative-left-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) {y : ℝ l2} → is-nonnegative-ℝ (real-ℝ⁺ x *ℝ y) →
    is-nonnegative-ℝ y
  is-nonnegative-is-nonnegative-left-mul-ℝ⁺ x⁺@(x , 0<x) {y = y} 0≤xy =
    reflects-leq-left-mul-ℝ⁺
      ( x⁺)
      ( zero-ℝ)
      ( y)
      ( preserves-leq-left-sim-ℝ
        ( symmetric-sim-ℝ (right-zero-law-mul-ℝ _))
        ( 0≤xy))
```

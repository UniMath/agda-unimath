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

### For every nonnegative real number `x`, there is a `q : ℚ⁺` such that `qx < 1`

```agda
abstract
  exists-ℚ⁺-mul-le-one-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) →
    exists ℚ⁺ (λ q → le-prop-ℝ⁰⁺ (nonnegative-real-ℚ⁺ q *ℝ⁰⁺ x) one-ℝ⁰⁺)
  exists-ℚ⁺-mul-le-one-ℝ⁰⁺ x⁰⁺@(x , _) =
    let
      open do-syntax-trunc-Prop (∃ ℚ⁺ (λ q → le-prop-ℝ (real-ℚ⁺ q *ℝ x) one-ℝ))
    in do
      (p , x<p) ← exists-ℚ⁺-in-upper-cut-ℝ⁰⁺ x⁰⁺
      intro-exists
        ( inv-ℚ⁺ p)
        ( tr
          ( le-ℝ _)
          ( equational-reasoning
            real-ℚ⁺ (inv-ℚ⁺ p) *ℝ real-ℚ⁺ p
            ＝ real-ℚ⁺ (inv-ℚ⁺ p *ℚ⁺ p)
              by mul-real-ℚ _ _
            ＝ one-ℝ
              by ap real-ℚ⁺ (left-inverse-law-mul-ℚ⁺ p))
          ( preserves-le-left-mul-ℝ⁺
            ( positive-real-ℚ⁺ (inv-ℚ⁺ p))
            ( le-real-is-in-upper-cut-ℚ x x<p)))
```

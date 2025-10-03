# The positive, negative, and nonnegative rational numbers

```agda
module elementary-number-theory.positive-and-negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

In this file, we outline basic relations between
[negative](elementary-number-theory.negative-rational-numbers.md),
[nonnegative](elementary-number-theory.nonnegative-rational-numbers.md),
[positive](elementary-number-theory.positive-rational-numbers.md), and
[nonpositive](elementary-number-theory.nonpositive-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md).

## Properties

### Dichotomies

#### A rational number is either negative or nonnegative

```agda
abstract
  decide-is-negative-is-nonnegative-ℚ :
    (q : ℚ) →
    is-negative-ℚ q + is-nonnegative-ℚ q
  decide-is-negative-is-nonnegative-ℚ q =
    map-coproduct
      ( is-negative-le-zero-ℚ q)
      ( is-nonnegative-leq-zero-ℚ q)
      ( decide-le-leq-ℚ q zero-ℚ)
```

#### A rational number is either positive or nonpositive

```agda
abstract
  decide-is-positive-is-nonpositive-ℚ :
    (q : ℚ) →
    is-positive-ℚ q + is-nonpositive-ℚ q
  decide-is-positive-is-nonpositive-ℚ q =
    map-coproduct
      ( is-positive-le-zero-ℚ q)
      ( is-nonpositive-leq-zero-ℚ q)
      ( decide-le-leq-ℚ zero-ℚ q)
```

### Trichotomies

#### A rational number is either negative, zero, or positive

```agda
abstract
  trichotomy-sign-ℚ :
    {l : Level} {A : UU l} (x : ℚ) →
    ( is-negative-ℚ x → A) →
    ( x ＝ zero-ℚ → A) →
    ( is-positive-ℚ x → A) →
    A
  trichotomy-sign-ℚ x neg zero pos =
    trichotomy-le-ℚ
      ( x)
      ( zero-ℚ)
      ( λ x<0 → neg (is-negative-le-zero-ℚ x x<0))
      ( zero)
      ( λ 0<x → pos (is-positive-le-zero-ℚ x 0<x))
```

### Inequalities

#### A negative rational number is less than a nonnegative rational number

```agda
abstract
  le-negative-nonnegative-ℚ :
    (p : ℚ⁻) (q : ℚ⁰⁺) → le-ℚ (rational-ℚ⁻ p) (rational-ℚ⁰⁺ q)
  le-negative-nonnegative-ℚ (p , neg-p) (q , nonneg-q) =
    concatenate-le-leq-ℚ p zero-ℚ q
      ( le-zero-is-negative-ℚ p neg-p)
      ( leq-zero-is-nonnegative-ℚ q nonneg-q)
```

#### A nonpositive rational number is less than a positive rational number

```agda
abstract
  le-nonpositive-positive-ℚ :
    (p : ℚ⁰⁻) (q : ℚ⁺) → le-ℚ (rational-ℚ⁰⁻ p) (rational-ℚ⁺ q)
  le-nonpositive-positive-ℚ (p , nonpos-p) (q , pos-q) =
    concatenate-leq-le-ℚ p zero-ℚ q
      ( leq-zero-is-nonpositive-ℚ p nonpos-p)
      ( le-zero-is-positive-ℚ q pos-q)
```

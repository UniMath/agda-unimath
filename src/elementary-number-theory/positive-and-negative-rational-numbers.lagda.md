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

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
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

#### A rational number is not both positive and negative

```agda
abstract
  is-not-negative-and-positive-ℚ :
    (q : ℚ) → ¬ (is-negative-ℚ q × is-positive-ℚ q)
  is-not-negative-and-positive-ℚ q (is-neg-q , is-pos-q) =
    not-leq-le-ℚ q zero-ℚ
      ( le-zero-is-negative-ℚ q is-neg-q)
      ( leq-le-ℚ (le-zero-is-positive-ℚ q is-pos-q))
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

#### A negative rational number is less than a positive rational number

```agda
abstract
  le-negative-positive-ℚ :
    (p : ℚ⁻) (q : ℚ⁺) → le-ℚ (rational-ℚ⁻ p) (rational-ℚ⁺ q)
  le-negative-positive-ℚ (p , neg-p) (q , pos-q) =
    transitive-le-ℚ p zero-ℚ q
      ( le-zero-is-positive-ℚ q pos-q)
      ( le-zero-is-negative-ℚ p neg-p)

  leq-negative-positive-ℚ :
    (p : ℚ⁻) (q : ℚ⁺) → leq-ℚ (rational-ℚ⁻ p) (rational-ℚ⁺ q)
  leq-negative-positive-ℚ p q = leq-le-ℚ (le-negative-positive-ℚ p q)
```

### If `p < q` and `p` is nonnegative, then `q` is positive

```agda
abstract
  is-positive-le-ℚ⁰⁺ :
    (p : ℚ⁰⁺) (q : ℚ) → le-ℚ (rational-ℚ⁰⁺ p) q → is-positive-ℚ q
  is-positive-le-ℚ⁰⁺ (p , nonneg-p) q p<q =
    is-positive-le-zero-ℚ
      ( q)
      ( concatenate-leq-le-ℚ _ _ _ (leq-zero-is-nonnegative-ℚ p nonneg-p) p<q)

  is-nonnegative-le-ℚ⁰⁺ :
    (p : ℚ⁰⁺) (q : ℚ) → le-ℚ (rational-ℚ⁰⁺ p) q → is-nonnegative-ℚ q
  is-nonnegative-le-ℚ⁰⁺ p q p<q =
    is-nonnegative-is-positive-ℚ q (is-positive-le-ℚ⁰⁺ p q p<q)
```

### If `p ≤ q` and `p` is nonnegative, then `q` is nonnegative

```agda
abstract
  is-nonnegative-leq-ℚ⁰⁺ :
    (p : ℚ⁰⁺) (q : ℚ) → leq-ℚ (rational-ℚ⁰⁺ p) q → is-nonnegative-ℚ q
  is-nonnegative-leq-ℚ⁰⁺ (p , is-nonneg-p) q p≤q =
    is-nonnegative-leq-zero-ℚ
      ( q)
      ( transitive-leq-ℚ zero-ℚ p q
        ( p≤q)
        ( leq-zero-is-nonnegative-ℚ p is-nonneg-p))
```

### Nonpositivity is negated positivity

```agda
abstract
  not-is-positive-is-nonpositive-ℚ :
    {q : ℚ} → is-nonpositive-ℚ q → ¬ (is-positive-ℚ q)
  not-is-positive-is-nonpositive-ℚ {q} is-nonpos-q is-pos-q =
    not-leq-le-ℚ zero-ℚ q
      ( le-zero-is-positive-ℚ q is-pos-q)
      ( leq-zero-is-nonpositive-ℚ q is-nonpos-q)

  is-nonpositive-not-is-positive-ℚ :
    {q : ℚ} → ¬ (is-positive-ℚ q) → is-nonpositive-ℚ q
  is-nonpositive-not-is-positive-ℚ {q} ¬is-pos-q =
    rec-coproduct
      ( ex-falso ∘ ¬is-pos-q)
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ q)

  is-nonpositive-iff-not-is-positive-ℚ :
    (q : ℚ) → is-nonpositive-ℚ q ↔ (¬ (is-positive-ℚ q))
  is-nonpositive-iff-not-is-positive-ℚ _ =
    ( not-is-positive-is-nonpositive-ℚ , is-nonpositive-not-is-positive-ℚ)
```

### Nonnegativity is negated negativity

```agda
abstract
  not-is-negative-is-nonnegative-ℚ :
    {q : ℚ} → is-nonnegative-ℚ q → ¬ (is-negative-ℚ q)
  not-is-negative-is-nonnegative-ℚ {q} is-nonneg-q is-neg-q =
    not-leq-le-ℚ q zero-ℚ
      ( le-zero-is-negative-ℚ q is-neg-q)
      ( leq-zero-is-nonnegative-ℚ q is-nonneg-q)

  is-nonnegative-not-is-negative-ℚ :
    {q : ℚ} → ¬ (is-negative-ℚ q) → is-nonnegative-ℚ q
  is-nonnegative-not-is-negative-ℚ {q} ¬is-neg-q =
    rec-coproduct
      ( ex-falso ∘ ¬is-neg-q)
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ q)

  is-nonnegative-iff-not-is-negative-ℚ :
    (q : ℚ) → is-nonnegative-ℚ q ↔ (¬ (is-negative-ℚ q))
  is-nonnegative-iff-not-is-negative-ℚ _ =
    ( not-is-negative-is-nonnegative-ℚ , is-nonnegative-not-is-negative-ℚ)
```

### If `p < q` and `q` is nonpositive, then `p` is negative

```agda
abstract
  is-negative-le-ℚ⁰⁻ :
    (q : ℚ⁰⁻) (p : ℚ) → le-ℚ p (rational-ℚ⁰⁻ q) → is-negative-ℚ p
  is-negative-le-ℚ⁰⁻ (q , nonpos-q) p p<q =
    is-negative-le-zero-ℚ
      ( p)
      ( concatenate-le-leq-ℚ p q zero-ℚ
        ( p<q)
        ( leq-zero-is-nonpositive-ℚ q nonpos-q))
```

### If `p ≤ q` and `q` is nonpositive, then `p` is nonpositive

```agda
abstract
  is-nonpositive-leq-ℚ⁰⁻ :
    (q : ℚ⁰⁻) (p : ℚ) → leq-ℚ p (rational-ℚ⁰⁻ q) → is-nonpositive-ℚ p
  is-nonpositive-leq-ℚ⁰⁻ (q , nonpos-q) p p≤q =
    is-nonpositive-leq-zero-ℚ
      ( p)
      ( transitive-leq-ℚ p q zero-ℚ
        ( leq-zero-is-nonpositive-ℚ q nonpos-q)
        ( p≤q))
```

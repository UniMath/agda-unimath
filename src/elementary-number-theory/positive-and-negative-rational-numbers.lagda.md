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
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.transport-along-identifications
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
      ( λ x<0 → neg (is-negative-le-zero-ℚ x<0))
      ( zero)
      ( λ 0<x → pos (is-positive-le-zero-ℚ 0<x))
```

### Dichotomies

#### A rational number is either negative or nonnegative

```agda
abstract
  decide-is-negative-is-nonnegative-ℚ :
    (q : ℚ) →
    is-negative-ℚ q + is-nonnegative-ℚ q
  decide-is-negative-is-nonnegative-ℚ q =
    map-coproduct
      ( is-negative-le-zero-ℚ)
      ( is-nonnegative-leq-zero-ℚ)
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
      ( is-positive-le-zero-ℚ)
      ( is-nonpositive-leq-zero-ℚ)
      ( decide-le-leq-ℚ zero-ℚ q)
```

#### A rational number is nonpositive or nonnegative

```agda
abstract
  is-nonpositive-or-nonnegative-ℚ :
    (q : ℚ) →
    is-nonpositive-ℚ q + is-nonnegative-ℚ q
  is-nonpositive-or-nonnegative-ℚ q =
    map-coproduct
      ( is-nonpositive-leq-zero-ℚ)
      ( is-nonnegative-leq-zero-ℚ)
      ( linear-leq-ℚ q zero-ℚ)
```

### If a rational number is nonzero, it is negative or positive

```agda
decide-is-negative-is-positive-is-nonzero-ℚ :
  {q : ℚ} → is-nonzero-ℚ q → is-negative-ℚ q + is-positive-ℚ q
decide-is-negative-is-positive-is-nonzero-ℚ {q} q≠0 =
  trichotomy-sign-ℚ q
    ( inl)
    ( ex-falso ∘ q≠0)
    ( inr)
```

### Implications

#### Any positive rational number is nonnegative

```agda
opaque
  unfolding is-nonnegative-ℚ is-positive-ℚ

  is-nonnegative-is-positive-ℚ : {q : ℚ} → is-positive-ℚ q → is-nonnegative-ℚ q
  is-nonnegative-is-positive-ℚ = is-nonnegative-is-positive-ℤ

nonnegative-ℚ⁺ : ℚ⁺ → ℚ⁰⁺
nonnegative-ℚ⁺ (q , H) = (q , is-nonnegative-is-positive-ℚ H)
```

### Any negative rational number is nonpositive

```agda
opaque
  unfolding is-negative-ℚ is-nonpositive-ℚ

  is-nonpositive-is-negative-ℚ : {q : ℚ} → is-negative-ℚ q → is-nonpositive-ℚ q
  is-nonpositive-is-negative-ℚ = is-nonnegative-is-positive-ℚ

nonpositive-ℚ⁻ : ℚ⁻ → ℚ⁰⁻
nonpositive-ℚ⁻ (q , H) = (q , is-nonpositive-is-negative-ℚ H)
```

### Operations

#### The negation of a positive rational number is negative

```agda
opaque
  unfolding is-negative-ℚ

  is-negative-neg-is-positive-ℚ :
    {q : ℚ} → is-positive-ℚ q → is-negative-ℚ (neg-ℚ q)
  is-negative-neg-is-positive-ℚ = inv-tr is-positive-ℚ (neg-neg-ℚ _)

neg-ℚ⁺ : ℚ⁺ → ℚ⁻
neg-ℚ⁺ (q , is-pos-q) =
  (neg-ℚ q , is-negative-neg-is-positive-ℚ is-pos-q)
```

#### The negation of a negative rational number is positive

```agda
opaque
  unfolding is-negative-ℚ

  is-positive-neg-is-negative-ℚ :
    {q : ℚ} → is-negative-ℚ q → is-positive-ℚ (neg-ℚ q)
  is-positive-neg-is-negative-ℚ = id

neg-ℚ⁻ : ℚ⁻ → ℚ⁺
neg-ℚ⁻ (q , is-neg-q) = (neg-ℚ q , is-positive-neg-is-negative-ℚ is-neg-q)
```

#### The negation of a nonnegative rational number is nonpositive

```agda
opaque
  unfolding is-nonpositive-ℚ

  is-nonpositive-neg-is-nonnegative-ℚ :
    {q : ℚ} → is-nonnegative-ℚ q → is-nonpositive-ℚ (neg-ℚ q)
  is-nonpositive-neg-is-nonnegative-ℚ = inv-tr is-nonnegative-ℚ (neg-neg-ℚ _)

neg-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁻
neg-ℚ⁰⁺ (q , is-nonneg-q) =
  ( neg-ℚ q , is-nonpositive-neg-is-nonnegative-ℚ is-nonneg-q)
```

#### The negation of a nonpositive rational number is nonnegative

```agda
opaque
  unfolding is-nonpositive-ℚ

  is-nonnegative-neg-is-nonpositive-ℚ :
    {q : ℚ} → is-nonpositive-ℚ q → is-nonnegative-ℚ (neg-ℚ q)
  is-nonnegative-neg-is-nonpositive-ℚ = id

neg-ℚ⁰⁻ : ℚ⁰⁻ → ℚ⁰⁺
neg-ℚ⁰⁻ (q , is-nonpos-q) =
  ( neg-ℚ q , is-nonnegative-neg-is-nonpositive-ℚ is-nonpos-q)
```

### Exclusive cases

#### A rational is not both negative and positive

```agda
abstract
  not-is-negative-is-positive-ℚ :
    {x : ℚ} → ¬ (is-negative-ℚ x × is-positive-ℚ x)
  not-is-negative-is-positive-ℚ {x} (N , P) =
    not-leq-le-ℚ
      ( zero-ℚ)
      ( x)
      ( le-zero-is-positive-ℚ P)
      ( leq-zero-is-negative-ℚ N)
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

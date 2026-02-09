# Nonnegative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integer-fractions
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A [rational number](elementary-number-theory.rational-numbers.md) `x` is said to
be
{{#concept "nonnegative" Disambiguation="rational number" Agda=is-nonnegative-ℚ}}
if its numerator is a
[nonnegative integer](elementary-number-theory.nonnegative-integers.md).

Nonnegative rational numbers are a [subsemigroup](group-theory.subsemigroups.md)
of the
[additive monoid of rational numbers](elementary-number-theory.additive-group-of-rational-numbers.md).

## Definitions

### The property of being a nonnegative rational number

```agda
module _
  (q : ℚ)
  where

  opaque
    is-nonnegative-ℚ : UU lzero
    is-nonnegative-ℚ = is-nonnegative-fraction-ℤ (fraction-ℚ q)

    is-prop-is-nonnegative-ℚ : is-prop is-nonnegative-ℚ
    is-prop-is-nonnegative-ℚ = is-prop-is-nonnegative-fraction-ℤ (fraction-ℚ q)

  is-nonnegative-prop-ℚ : Prop lzero
  pr1 is-nonnegative-prop-ℚ = is-nonnegative-ℚ
  pr2 is-nonnegative-prop-ℚ = is-prop-is-nonnegative-ℚ
```

### The type of nonnegative rational numbers

```agda
nonnegative-ℚ : UU lzero
nonnegative-ℚ = type-subtype is-nonnegative-prop-ℚ

ℚ⁰⁺ : UU lzero
ℚ⁰⁺ = nonnegative-ℚ

module _
  (x : nonnegative-ℚ)
  where

  rational-ℚ⁰⁺ : ℚ
  rational-ℚ⁰⁺ = pr1 x

  fraction-ℚ⁰⁺ : fraction-ℤ
  fraction-ℚ⁰⁺ = fraction-ℚ rational-ℚ⁰⁺

  numerator-ℚ⁰⁺ : ℤ
  numerator-ℚ⁰⁺ = numerator-ℚ rational-ℚ⁰⁺

  denominator-ℚ⁰⁺ : ℤ
  denominator-ℚ⁰⁺ = denominator-ℚ rational-ℚ⁰⁺

  is-nonnegative-rational-ℚ⁰⁺ : is-nonnegative-ℚ rational-ℚ⁰⁺
  is-nonnegative-rational-ℚ⁰⁺ = pr2 x

  opaque
    unfolding is-nonnegative-ℚ

    is-nonnegative-fraction-ℚ⁰⁺ : is-nonnegative-fraction-ℤ fraction-ℚ⁰⁺
    is-nonnegative-fraction-ℚ⁰⁺ = pr2 x

  is-nonnegative-numerator-ℚ⁰⁺ : is-nonnegative-ℤ numerator-ℚ⁰⁺
  is-nonnegative-numerator-ℚ⁰⁺ = is-nonnegative-fraction-ℚ⁰⁺

  is-positive-denominator-ℚ⁰⁺ : is-positive-ℤ denominator-ℚ⁰⁺
  is-positive-denominator-ℚ⁰⁺ = is-positive-denominator-ℚ rational-ℚ⁰⁺
```

## Properties

### Equality on nonnegative rational numbers

```agda
abstract
  eq-ℚ⁰⁺ : {x y : ℚ⁰⁺} → rational-ℚ⁰⁺ x ＝ rational-ℚ⁰⁺ y → x ＝ y
  eq-ℚ⁰⁺ {x} {y} = eq-type-subtype is-nonnegative-prop-ℚ

  is-injective-rational-ℚ⁰⁺ : is-injective rational-ℚ⁰⁺
  is-injective-rational-ℚ⁰⁺ = eq-ℚ⁰⁺

  is-emb-rational-ℚ⁰⁺ : is-emb rational-ℚ⁰⁺
  is-emb-rational-ℚ⁰⁺ =
    is-emb-is-injective is-set-ℚ is-injective-rational-ℚ⁰⁺
```

### The nonnegative rational numbers form a set

```agda
is-set-ℚ⁰⁺ : is-set ℚ⁰⁺
is-set-ℚ⁰⁺ = is-set-type-subtype is-nonnegative-prop-ℚ is-set-ℚ
```

### The rational image of a nonnegative integer is nonnegative

```agda
opaque
  unfolding is-nonnegative-ℚ

  is-nonnegative-rational-ℤ :
    {x : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℚ (rational-ℤ x)
  is-nonnegative-rational-ℤ H = H

nonnegative-rational-nonnegative-ℤ : nonnegative-ℤ → ℚ⁰⁺
nonnegative-rational-nonnegative-ℤ (x , x-is-neg) =
  ( rational-ℤ x , is-nonnegative-rational-ℤ x-is-neg)
```

### The images of natural numbers in the rationals are nonnegative

```agda
module _
  (n : ℕ)
  where

  opaque
    unfolding is-nonnegative-ℚ

    is-nonnegative-rational-ℕ : is-nonnegative-ℚ (rational-ℕ n)
    is-nonnegative-rational-ℕ = is-nonnegative-int-ℕ n

  nonnegative-rational-ℕ : ℚ⁰⁺
  nonnegative-rational-ℕ = (rational-ℕ n , is-nonnegative-rational-ℕ)

zero-ℚ⁰⁺ : ℚ⁰⁺
zero-ℚ⁰⁺ = nonnegative-rational-ℕ zero-ℕ

one-ℚ⁰⁺ : ℚ⁰⁺
one-ℚ⁰⁺ = nonnegative-rational-ℕ 1

is-nonnegative-one-ℚ : is-nonnegative-ℚ one-ℚ
is-nonnegative-one-ℚ = is-nonnegative-rational-ℕ 1
```

### The rational image of a nonnegative integer fraction is nonnegative

```agda
opaque
  unfolding is-nonnegative-ℚ rational-fraction-ℤ

  is-nonnegative-rational-fraction-ℤ :
    {x : fraction-ℤ} (P : is-nonnegative-fraction-ℤ x) →
    is-nonnegative-ℚ (rational-fraction-ℤ x)
  is-nonnegative-rational-fraction-ℤ {x} =
    is-nonnegative-sim-fraction-ℤ
      ( x)
      ( reduce-fraction-ℤ x)
      ( sim-reduced-fraction-ℤ x)
```

### A rational number `x` is nonnegative if and only if `0 ≤ x`

```agda
opaque
  unfolding is-nonnegative-ℚ leq-ℚ-Prop

  leq-zero-is-nonnegative-ℚ : {x : ℚ} → is-nonnegative-ℚ x → leq-ℚ zero-ℚ x
  leq-zero-is-nonnegative-ℚ {x} =
    is-nonnegative-eq-ℤ (inv (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x)))

  is-nonnegative-leq-zero-ℚ : {x : ℚ} → leq-ℚ zero-ℚ x → is-nonnegative-ℚ x
  is-nonnegative-leq-zero-ℚ {x} =
    is-nonnegative-eq-ℤ (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x))

is-nonnegative-iff-leq-zero-ℚ : (x : ℚ) → is-nonnegative-ℚ x ↔ leq-ℚ zero-ℚ x
is-nonnegative-iff-leq-zero-ℚ x =
  ( leq-zero-is-nonnegative-ℚ ,
    is-nonnegative-leq-zero-ℚ)

abstract
  leq-zero-rational-ℚ⁰⁺ : (p : ℚ⁰⁺) → leq-ℚ zero-ℚ (rational-ℚ⁰⁺ p)
  leq-zero-rational-ℚ⁰⁺ (p , is-nonneg-p) =
    leq-zero-is-nonnegative-ℚ is-nonneg-p
```

### The successor of a nonnegative rational number is positive

```agda
abstract
  is-positive-succ-is-nonnegative-ℚ :
    (q : ℚ) → is-nonnegative-ℚ q → is-positive-ℚ (succ-ℚ q)
  is-positive-succ-is-nonnegative-ℚ q H =
    is-positive-le-zero-ℚ
      ( concatenate-leq-le-ℚ
        ( zero-ℚ)
        ( q)
        ( succ-ℚ q)
        ( leq-zero-is-nonnegative-ℚ H)
        ( le-left-add-rational-ℚ⁺ q one-ℚ⁺))

positive-succ-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁺
positive-succ-ℚ⁰⁺ (q , H) = (succ-ℚ q , is-positive-succ-is-nonnegative-ℚ q H)
```

### `x ≤ y` if and only if `y - x` is nonnegative

```agda
abstract
  is-nonnegative-diff-iff-leq-ℚ :
    (x y : ℚ) → (is-nonnegative-ℚ (y -ℚ x)) ↔ (leq-ℚ x y)
  is-nonnegative-diff-iff-leq-ℚ x y =
    iff-translate-diff-leq-zero-ℚ x y ∘iff
    is-nonnegative-iff-leq-zero-ℚ (y -ℚ x)

  is-nonnegative-diff-leq-ℚ : (x y : ℚ) → leq-ℚ x y → is-nonnegative-ℚ (y -ℚ x)
  is-nonnegative-diff-leq-ℚ x y =
    backward-implication (is-nonnegative-diff-iff-leq-ℚ x y)

  leq-is-nonnegative-diff-ℚ : (x y : ℚ) → is-nonnegative-ℚ (y -ℚ x) → leq-ℚ x y
  leq-is-nonnegative-diff-ℚ x y =
    forward-implication (is-nonnegative-diff-iff-leq-ℚ x y)

nonnegative-diff-leq-ℚ : (x y : ℚ) → leq-ℚ x y → ℚ⁰⁺
nonnegative-diff-leq-ℚ x y x≤y = (y -ℚ x , is-nonnegative-diff-leq-ℚ x y x≤y)
```

### If `x ≤ y` and `x` is nonnegative, then `y` is nonnegative

```agda
abstract
  is-nonnegative-leq-ℚ⁰⁺ :
    (x : ℚ⁰⁺) (y : ℚ) → leq-ℚ (rational-ℚ⁰⁺ x) y →
    is-nonnegative-ℚ y
  is-nonnegative-leq-ℚ⁰⁺ (x , is-nonneg-x) y x≤y =
    is-nonnegative-leq-zero-ℚ
      ( transitive-leq-ℚ zero-ℚ x y
        ( x≤y)
        ( leq-zero-is-nonnegative-ℚ is-nonneg-x))
```

### If `x < y` and `x` is nonnegative, then `y` is nonnegative

```agda
abstract
  is-nonnegative-le-ℚ⁰⁺ :
    (x : ℚ⁰⁺) (y : ℚ) → le-ℚ (rational-ℚ⁰⁺ x) y →
    is-nonnegative-ℚ y
  is-nonnegative-le-ℚ⁰⁺ x y x<y =
    is-nonnegative-leq-ℚ⁰⁺ x y (leq-le-ℚ x<y)
```

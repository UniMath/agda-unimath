# Negative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.negative-integer-fractions
open import elementary-number-theory.negative-integers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
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
be {{#concept "negative" Disambiguation="rational number" Agda=is-negative-ℚ}}
if its negation is positive.

Negative rational numbers are a [subsemigroup](group-theory.subsemigroups.md) of
the
[additive monoid of rational numbers](elementary-number-theory.additive-group-of-rational-numbers.md).

## Definitions

### The property of being a negative rational number

```agda
module _
  (q : ℚ)
  where

  opaque
    is-negative-ℚ : UU lzero
    is-negative-ℚ = is-positive-ℚ (neg-ℚ q)

    is-prop-is-negative-ℚ : is-prop is-negative-ℚ
    is-prop-is-negative-ℚ = is-prop-is-positive-ℚ (neg-ℚ q)

  is-negative-prop-ℚ : Prop lzero
  pr1 is-negative-prop-ℚ = is-negative-ℚ
  pr2 is-negative-prop-ℚ = is-prop-is-negative-ℚ
```

### The type of negative rational numbers

```agda
negative-ℚ : UU lzero
negative-ℚ = type-subtype is-negative-prop-ℚ

ℚ⁻ : UU lzero
ℚ⁻ = negative-ℚ

module _
  (x : negative-ℚ)
  where

  rational-ℚ⁻ : ℚ
  rational-ℚ⁻ = pr1 x

  fraction-ℚ⁻ : fraction-ℤ
  fraction-ℚ⁻ = fraction-ℚ rational-ℚ⁻

  numerator-ℚ⁻ : ℤ
  numerator-ℚ⁻ = numerator-ℚ rational-ℚ⁻

  denominator-ℚ⁻ : ℤ
  denominator-ℚ⁻ = denominator-ℚ rational-ℚ⁻

  is-negative-rational-ℚ⁻ : is-negative-ℚ rational-ℚ⁻
  is-negative-rational-ℚ⁻ = pr2 x

  opaque
    unfolding is-negative-ℚ is-positive-ℚ neg-ℚ

    is-negative-fraction-ℚ⁻ : is-negative-fraction-ℤ fraction-ℚ⁻
    is-negative-fraction-ℚ⁻ =
      tr
        ( is-negative-ℤ)
        ( neg-neg-ℤ _)
        ( is-negative-neg-is-positive-ℤ is-negative-rational-ℚ⁻)

  is-negative-numerator-ℚ⁻ : is-negative-ℤ numerator-ℚ⁻
  is-negative-numerator-ℚ⁻ = is-negative-fraction-ℚ⁻

  is-positive-denominator-ℚ⁻ : is-positive-ℤ denominator-ℚ⁻
  is-positive-denominator-ℚ⁻ = is-positive-denominator-ℚ rational-ℚ⁻

abstract
  eq-ℚ⁻ : {x y : ℚ⁻} → rational-ℚ⁻ x ＝ rational-ℚ⁻ y → x ＝ y
  eq-ℚ⁻ {x} {y} = eq-type-subtype is-negative-prop-ℚ
```

## Properties

### The negative rational numbers form a set

```agda
is-set-ℚ⁻ : is-set ℚ⁻
is-set-ℚ⁻ = is-set-type-subtype is-negative-prop-ℚ is-set-ℚ
```

### The rational image of a negative integer is negative

```agda
opaque
  unfolding is-negative-ℚ is-positive-ℚ neg-ℚ

  is-negative-rational-ℤ :
    (x : ℤ) → is-negative-ℤ x → is-negative-ℚ (rational-ℤ x)
  is-negative-rational-ℤ _ = is-positive-neg-is-negative-ℤ

negative-rational-negative-ℤ : negative-ℤ → ℚ⁻
negative-rational-negative-ℤ (x , x-is-neg) =
  rational-ℤ x , is-negative-rational-ℤ x x-is-neg

neg-one-ℚ⁻ : ℚ⁻
neg-one-ℚ⁻ = (neg-one-ℚ , is-negative-rational-ℤ _ _)
```

### The rational image of a negative integer fraction is negative

```agda
opaque
  unfolding is-negative-ℚ

  is-negative-rational-fraction-ℤ :
    {x : fraction-ℤ} → is-negative-fraction-ℤ x →
    is-negative-ℚ (rational-fraction-ℤ x)
  is-negative-rational-fraction-ℤ {x} P =
    tr
      ( is-positive-ℚ)
      ( neg-rational-fraction-ℤ _)
      ( is-positive-rational-fraction-ℤ
        ( is-positive-neg-negative-fraction-ℤ x P))
```

### A rational number `x` is negative if and only if `x < 0`

```agda
opaque
  unfolding is-negative-ℚ

  le-zero-is-negative-ℚ : {x : ℚ} → is-negative-ℚ x → le-ℚ x zero-ℚ
  le-zero-is-negative-ℚ {x} is-neg-x =
    binary-tr
      ( le-ℚ)
      ( neg-neg-ℚ x)
      ( neg-zero-ℚ)
      ( neg-le-ℚ (le-zero-is-positive-ℚ is-neg-x))

  is-negative-le-zero-ℚ : {x : ℚ} → le-ℚ x zero-ℚ → is-negative-ℚ x
  is-negative-le-zero-ℚ {x} x<0 =
    is-positive-le-zero-ℚ
      ( tr
        ( λ y → le-ℚ y (neg-ℚ x))
        ( neg-zero-ℚ)
        ( neg-le-ℚ x<0))

is-negative-iff-le-zero-ℚ : (x : ℚ) → is-negative-ℚ x ↔ le-ℚ x zero-ℚ
is-negative-iff-le-zero-ℚ x =
  ( le-zero-is-negative-ℚ ,
    is-negative-le-zero-ℚ)

abstract
  leq-zero-is-negative-ℚ : {x : ℚ} → is-negative-ℚ x → leq-ℚ x zero-ℚ
  leq-zero-is-negative-ℚ is-neg-x = leq-le-ℚ (le-zero-is-negative-ℚ is-neg-x)
```

### The difference of a rational number with a greater rational number is negative

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  opaque
    unfolding is-negative-ℚ

    is-negative-diff-le-ℚ : is-negative-ℚ (x -ℚ y)
    is-negative-diff-le-ℚ =
      inv-tr
        ( is-positive-ℚ)
        ( distributive-neg-diff-ℚ x y)
        ( is-positive-diff-le-ℚ x y H)

  negative-diff-le-ℚ : ℚ⁻
  negative-diff-le-ℚ = x -ℚ y , is-negative-diff-le-ℚ
```

### Negative rational numbers are nonzero

```agda
opaque
  unfolding is-negative-ℚ

  is-nonzero-is-negative-ℚ : {x : ℚ} → is-negative-ℚ x → is-nonzero-ℚ x
  is-nonzero-is-negative-ℚ {x} H =
    tr
      ( is-nonzero-ℚ)
      ( neg-neg-ℚ x)
      ( is-nonzero-neg-ℚ (is-nonzero-is-positive-ℚ H))

nonzero-ℚ⁻ : ℚ⁻ → nonzero-ℚ
nonzero-ℚ⁻ (x , N) = (x , is-nonzero-is-negative-ℚ N)
```

### Inequality on negative rational numbers

```agda
leq-ℚ⁻ : Relation lzero ℚ⁻
leq-ℚ⁻ p q = leq-ℚ (rational-ℚ⁻ p) (rational-ℚ⁻ q)

le-ℚ⁻ : Relation lzero ℚ⁻
le-ℚ⁻ p q = le-ℚ (rational-ℚ⁻ p) (rational-ℚ⁻ q)
```

### If `p ≤ q` for negative `q`, then `p` is negative

```agda
abstract
  is-negative-leq-ℚ⁻ :
    (q : ℚ⁻) (p : ℚ) → leq-ℚ p (rational-ℚ⁻ q) → is-negative-ℚ p
  is-negative-leq-ℚ⁻ (q , neg-q) p p≤q =
    is-negative-le-zero-ℚ
      ( concatenate-leq-le-ℚ p q zero-ℚ p≤q (le-zero-is-negative-ℚ neg-q))

  is-negative-le-ℚ⁻ :
    (q : ℚ⁻) (p : ℚ) → le-ℚ p (rational-ℚ⁻ q) → is-negative-ℚ p
  is-negative-le-ℚ⁻ q p p<q = is-negative-leq-ℚ⁻ q p (leq-le-ℚ p<q)
```

### There is no greatest negative rational number

```agda
opaque
  mediant-zero-ℚ⁻ : ℚ⁻ → ℚ⁻
  mediant-zero-ℚ⁻ (q , is-neg-q) =
    ( mediant-ℚ q zero-ℚ ,
      is-negative-le-zero-ℚ
      ( le-right-mediant-ℚ _ _ (le-zero-is-negative-ℚ is-neg-q)))

  le-mediant-zero-ℚ⁻ :
    (q : ℚ⁻) → le-ℚ (rational-ℚ⁻ q) (rational-ℚ⁻ (mediant-zero-ℚ⁻ q))
  le-mediant-zero-ℚ⁻ (q , is-neg-q) =
    le-left-mediant-ℚ _ _ (le-zero-is-negative-ℚ is-neg-q)

rational-mediant-zero-ℚ⁻ : ℚ⁻ → ℚ
rational-mediant-zero-ℚ⁻ q = rational-ℚ⁻ (mediant-zero-ℚ⁻ q)
```

### The negative rational numbers are invertible elements of the multiplicative monoid of rational numbers

```agda
opaque
  inv-ℚ⁻ : ℚ⁻ → ℚ⁻
  inv-ℚ⁻ q = neg-ℚ⁺ (inv-ℚ⁺ (neg-ℚ⁻ q))

  left-inverse-law-mul-ℚ⁻ :
    (q : ℚ⁻) → rational-ℚ⁻ (inv-ℚ⁻ q) *ℚ rational-ℚ⁻ q ＝ one-ℚ
  left-inverse-law-mul-ℚ⁻ q =
    inv (swap-neg-mul-ℚ _ _) ∙
    ap rational-ℚ⁺ (left-inverse-law-mul-ℚ⁺ (neg-ℚ⁻ q))

  right-inverse-law-mul-ℚ⁻ :
    (q : ℚ⁻) → rational-ℚ⁻ q *ℚ rational-ℚ⁻ (inv-ℚ⁻ q) ＝ one-ℚ
  right-inverse-law-mul-ℚ⁻ q =
    swap-neg-mul-ℚ _ _ ∙
    ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ (neg-ℚ⁻ q))
```

### Inequality on negative rational numbers

```agda
leq-ℚ⁻ : Relation lzero ℚ⁻
leq-ℚ⁻ p q = leq-ℚ (rational-ℚ⁻ p) (rational-ℚ⁻ q)

le-ℚ⁻ : Relation lzero ℚ⁻
le-ℚ⁻ p q = le-ℚ (rational-ℚ⁻ p) (rational-ℚ⁻ q)
```

### Inversion reverses inequality on negative rational numbers

```agda
opaque
  unfolding inv-ℚ⁻

  reverses-leq-inv-ℚ⁻ :
    (p q : ℚ⁻) → leq-ℚ⁻ p q → leq-ℚ⁻ (inv-ℚ⁻ q) (inv-ℚ⁻ p)
  reverses-leq-inv-ℚ⁻ p q p≤q =
    neg-leq-ℚ
      ( rational-ℚ⁺ (inv-ℚ⁺ (neg-ℚ⁻ p)))
      ( rational-ℚ⁺ (inv-ℚ⁺ (neg-ℚ⁻ q)))
      ( inv-leq-ℚ⁺
        ( neg-ℚ⁻ q)
        ( neg-ℚ⁻ p)
        ( neg-leq-ℚ _ _ p≤q))
```

### Inversion reverses strict inequality on negative rational numbers

```agda
opaque
  unfolding inv-ℚ⁻

  reverses-le-inv-ℚ⁻ :
    (p q : ℚ⁻) → le-ℚ⁻ p q → le-ℚ⁻ (inv-ℚ⁻ q) (inv-ℚ⁻ p)
  reverses-le-inv-ℚ⁻ p q p<q =
    neg-le-ℚ
      ( rational-ℚ⁺ (inv-ℚ⁺ (neg-ℚ⁻ p)))
      ( rational-ℚ⁺ (inv-ℚ⁺ (neg-ℚ⁻ q)))
      ( inv-le-ℚ⁺
        ( neg-ℚ⁻ q)
        ( neg-ℚ⁻ p)
        ( neg-le-ℚ _ _ p<q))
```

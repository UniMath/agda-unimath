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
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
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
    unfolding neg-ℚ

    is-negative-fraction-ℚ⁻ : is-negative-fraction-ℤ fraction-ℚ⁻
    is-negative-fraction-ℚ⁻ =
      tr
        ( is-negative-fraction-ℤ)
        ( neg-neg-fraction-ℤ fraction-ℚ⁻)
        ( is-negative-neg-positive-fraction-ℤ
          ( neg-fraction-ℤ fraction-ℚ⁻)
          ( is-negative-rational-ℚ⁻))

  is-negative-numerator-ℚ⁻ : is-negative-ℤ numerator-ℚ⁻
  is-negative-numerator-ℚ⁻ = is-negative-fraction-ℚ⁻

  is-positive-denominator-ℚ⁻ : is-positive-ℤ denominator-ℚ⁻
  is-positive-denominator-ℚ⁻ = is-positive-denominator-ℚ rational-ℚ⁻

  neg-ℚ⁻ : ℚ⁺
  neg-ℚ⁻ = (neg-ℚ rational-ℚ⁻) , is-negative-rational-ℚ⁻

neg-ℚ⁺ : ℚ⁺ → ℚ⁻
neg-ℚ⁺ (q , q-is-pos) = neg-ℚ q , inv-tr is-positive-ℚ (neg-neg-ℚ q) q-is-pos

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
  unfolding neg-ℚ

  is-negative-rational-ℤ :
    (x : ℤ) → is-negative-ℤ x → is-negative-ℚ (rational-ℤ x)
  is-negative-rational-ℤ _ = is-positive-neg-is-negative-ℤ

negative-rational-negative-ℤ : negative-ℤ → ℚ⁻
negative-rational-negative-ℤ (x , x-is-neg) =
  rational-ℤ x , is-negative-rational-ℤ x x-is-neg
```

### The rational image of a negative integer fraction is negative

```agda
opaque
  unfolding neg-ℚ
  unfolding rational-fraction-ℤ

  is-negative-rational-fraction-ℤ :
    {x : fraction-ℤ} (P : is-negative-fraction-ℤ x) →
    is-negative-ℚ (rational-fraction-ℤ x)
  is-negative-rational-fraction-ℤ P =
    is-positive-neg-is-negative-ℤ (is-negative-reduce-fraction-ℤ P)
```

### A rational number `x` is negative if and only if `x < 0`

```agda
module _
  (x : ℚ)
  where

  opaque
    unfolding neg-ℚ

    le-zero-is-negative-ℚ : is-negative-ℚ x → le-ℚ x zero-ℚ
    le-zero-is-negative-ℚ x-is-neg =
      tr
        ( λ y → le-ℚ y zero-ℚ)
        ( neg-neg-ℚ x)
        ( neg-le-ℚ zero-ℚ (neg-ℚ x) (le-zero-is-positive-ℚ (neg-ℚ x) x-is-neg))

    is-negative-le-zero-ℚ : le-ℚ x zero-ℚ → is-negative-ℚ x
    is-negative-le-zero-ℚ x-is-neg =
      is-positive-le-zero-ℚ (neg-ℚ x) (neg-le-ℚ x zero-ℚ x-is-neg)

    is-negative-iff-le-zero-ℚ : is-negative-ℚ x ↔ le-ℚ x zero-ℚ
    is-negative-iff-le-zero-ℚ =
      le-zero-is-negative-ℚ ,
      is-negative-le-zero-ℚ
```

### The difference of a rational number with a greater rational number is negative

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  abstract
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
abstract
  is-nonzero-is-negative-ℚ : {x : ℚ} → is-negative-ℚ x → is-nonzero-ℚ x
  is-nonzero-is-negative-ℚ {x} H =
    tr
      ( is-nonzero-ℚ)
      ( neg-neg-ℚ x)
      ( is-nonzero-neg-ℚ (is-nonzero-is-positive-ℚ H))

nonzero-ℚ⁻ : ℚ⁻ → nonzero-ℚ
nonzero-ℚ⁻ (x , N) = (x , is-nonzero-is-negative-ℚ N)
```

### Multiplication by a negative rational number reverses inequality

```agda
module _
  (p : ℚ⁻)
  (q r : ℚ)
  (H : leq-ℚ q r)
  where

  abstract
    reverses-leq-right-mul-ℚ⁻ : leq-ℚ (r *ℚ rational-ℚ⁻ p) (q *ℚ rational-ℚ⁻ p)
    reverses-leq-right-mul-ℚ⁻ =
      binary-tr
        ( leq-ℚ)
        ( negative-law-mul-ℚ r (rational-ℚ⁻ p))
        ( negative-law-mul-ℚ q (rational-ℚ⁻ p))
        ( preserves-leq-right-mul-ℚ⁺
          ( neg-ℚ⁻ p)
          ( neg-ℚ r)
          ( neg-ℚ q)
          ( neg-leq-ℚ q r H))
```

### Multiplication by a negative rational number reverses strict inequality

```agda
module _
  (p : ℚ⁻)
  (q r : ℚ)
  (H : le-ℚ q r)
  where

  abstract
    reverses-le-right-mul-ℚ⁻ : le-ℚ (r *ℚ rational-ℚ⁻ p) (q *ℚ rational-ℚ⁻ p)
    reverses-le-right-mul-ℚ⁻ =
      binary-tr
        ( le-ℚ)
        ( negative-law-mul-ℚ r (rational-ℚ⁻ p))
        ( negative-law-mul-ℚ q (rational-ℚ⁻ p))
        ( preserves-le-right-mul-ℚ⁺
          ( neg-ℚ⁻ p)
          ( neg-ℚ r)
          ( neg-ℚ q)
          ( neg-le-ℚ q r H))

    reverses-le-left-mul-ℚ⁻ : le-ℚ (rational-ℚ⁻ p *ℚ r) (rational-ℚ⁻ p *ℚ q)
    reverses-le-left-mul-ℚ⁻ =
      binary-tr
        ( le-ℚ)
        ( commutative-mul-ℚ _ _)
        ( commutative-mul-ℚ _ _)
        ( reverses-le-right-mul-ℚ⁻)
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

### If `p ≤ q` for negative `q`, then `p` is negative

```agda
abstract
  is-negative-leq-ℚ⁻ :
    (q : ℚ⁻) (p : ℚ) → leq-ℚ p (rational-ℚ⁻ q) → is-negative-ℚ p
  is-negative-leq-ℚ⁻ (q , neg-q) p p≤q =
    is-negative-le-zero-ℚ
      ( p)
      ( concatenate-leq-le-ℚ p q zero-ℚ p≤q (le-zero-is-negative-ℚ q neg-q))

  is-negative-le-ℚ⁻ :
    (q : ℚ⁻) (p : ℚ) → le-ℚ p (rational-ℚ⁻ q) → is-negative-ℚ p
  is-negative-le-ℚ⁻ q p p<q = is-negative-leq-ℚ⁻ q p (leq-le-ℚ p<q)
```

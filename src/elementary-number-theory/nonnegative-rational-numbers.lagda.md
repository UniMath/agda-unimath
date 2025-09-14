# Nonnegative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-integer-fractions
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.inflationary-maps-posets
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

  is-nonnegative-fraction-ℚ⁰⁺ : is-nonnegative-fraction-ℤ fraction-ℚ⁰⁺
  is-nonnegative-fraction-ℚ⁰⁺ = pr2 x

  is-nonnegative-numerator-ℚ⁰⁺ : is-nonnegative-ℤ numerator-ℚ⁰⁺
  is-nonnegative-numerator-ℚ⁰⁺ = is-nonnegative-fraction-ℚ⁰⁺

  is-positive-denominator-ℚ⁰⁺ : is-positive-ℤ denominator-ℚ⁰⁺
  is-positive-denominator-ℚ⁰⁺ = is-positive-denominator-ℚ rational-ℚ⁰⁺

abstract
  eq-ℚ⁰⁺ : {x y : ℚ⁰⁺} → rational-ℚ⁰⁺ x ＝ rational-ℚ⁰⁺ y → x ＝ y
  eq-ℚ⁰⁺ {x} {y} = eq-type-subtype is-nonnegative-prop-ℚ

zero-ℚ⁰⁺ : ℚ⁰⁺
zero-ℚ⁰⁺ = zero-ℚ , _

one-ℚ⁰⁺ : ℚ⁰⁺
one-ℚ⁰⁺ = one-ℚ , _
```

## Properties

### The nonnegative rational numbers form a set

```agda
is-set-ℚ⁰⁺ : is-set ℚ⁰⁺
is-set-ℚ⁰⁺ = is-set-type-subtype is-nonnegative-prop-ℚ is-set-ℚ
```

### All positive rational numbers are nonnegative

```agda
abstract
  is-nonnegative-is-positive-ℚ : (q : ℚ) → is-positive-ℚ q → is-nonnegative-ℚ q
  is-nonnegative-is-positive-ℚ _ = is-nonnegative-is-positive-ℤ

nonnegative-ℚ⁺ : ℚ⁺ → ℚ⁰⁺
nonnegative-ℚ⁺ (q , H) = (q , is-nonnegative-is-positive-ℚ q H)
```

### The rational image of a nonnegative integer is nonnegative

```agda
abstract
  is-nonnegative-rational-ℤ :
    (x : ℤ) → is-nonnegative-ℤ x → is-nonnegative-ℚ (rational-ℤ x)
  is-nonnegative-rational-ℤ _ H = H

nonnegative-rational-nonnegative-ℤ : nonnegative-ℤ → ℚ⁰⁺
nonnegative-rational-nonnegative-ℤ (x , x-is-neg) =
  ( rational-ℤ x , is-nonnegative-rational-ℤ x x-is-neg)
```

### The rational image of a nonnegative integer fraction is nonnegative

```agda
opaque
  unfolding rational-fraction-ℤ

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
module _
  (x : ℚ)
  where

  opaque
    unfolding leq-ℚ-Prop

    leq-zero-is-nonnegative-ℚ : is-nonnegative-ℚ x → leq-ℚ zero-ℚ x
    leq-zero-is-nonnegative-ℚ =
      is-nonnegative-eq-ℤ (inv (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x)))

    is-nonnegative-leq-zero-ℚ : leq-ℚ zero-ℚ x → is-nonnegative-ℚ x
    is-nonnegative-leq-zero-ℚ =
      is-nonnegative-eq-ℤ (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x))

    is-nonnegative-iff-leq-zero-ℚ : is-nonnegative-ℚ x ↔ leq-ℚ zero-ℚ x
    is-nonnegative-iff-leq-zero-ℚ =
      ( leq-zero-is-nonnegative-ℚ ,
        is-nonnegative-leq-zero-ℚ)
```

### The successor of a nonnegative rational number is positive

```agda
abstract
  is-positive-succ-is-nonnegative-ℚ :
    (q : ℚ) → is-nonnegative-ℚ q → is-positive-ℚ (succ-ℚ q)
  is-positive-succ-is-nonnegative-ℚ q H =
    is-positive-le-zero-ℚ
      ( succ-ℚ q)
      ( concatenate-leq-le-ℚ
        ( zero-ℚ)
        ( q)
        ( succ-ℚ q)
        ( leq-zero-is-nonnegative-ℚ q H)
        ( le-left-add-rational-ℚ⁺ q one-ℚ⁺))

positive-succ-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁺
positive-succ-ℚ⁰⁺ (q , H) = (succ-ℚ q , is-positive-succ-is-nonnegative-ℚ q H)
```

### Multiplication by a nonnegative rational number preserves inequality

```agda
opaque
  unfolding leq-ℚ-Prop
  unfolding mul-ℚ

  preserves-leq-right-mul-ℚ⁰⁺ :
    (p : ℚ⁰⁺) (q r : ℚ) → leq-ℚ q r →
    leq-ℚ (q *ℚ rational-ℚ⁰⁺ p) (r *ℚ rational-ℚ⁰⁺ p)
  preserves-leq-right-mul-ℚ⁰⁺
    p⁺@((p@(np , dp , pos-dp) , _) , nonneg-np)
    (q@(nq , dq , _) , _)
    (r@(nr , dr , _) , _)
    q≤r =
      preserves-leq-rational-fraction-ℤ
        ( mul-fraction-ℤ q p)
        ( mul-fraction-ℤ r p)
        ( binary-tr
          ( leq-ℤ)
          ( interchange-law-mul-mul-ℤ _ _ _ _)
          ( interchange-law-mul-mul-ℤ _ _ _ _)
          ( preserves-leq-left-mul-nonnegative-ℤ
            ( np *ℤ dp ,
              is-nonnegative-mul-nonnegative-positive-ℤ nonneg-np pos-dp)
            ( nq *ℤ dr)
            ( nr *ℤ dq)
            ( q≤r)))

  preserves-leq-left-mul-ℚ⁰⁺ :
    (p : ℚ⁰⁺) (q r : ℚ) → leq-ℚ q r →
    leq-ℚ (rational-ℚ⁰⁺ p *ℚ q) (rational-ℚ⁰⁺ p *ℚ r)
  preserves-leq-left-mul-ℚ⁰⁺ p q r q≤r =
    binary-tr
      ( leq-ℚ)
      ( commutative-mul-ℚ q (rational-ℚ⁰⁺ p))
      ( commutative-mul-ℚ r (rational-ℚ⁰⁺ p))
      ( preserves-leq-right-mul-ℚ⁰⁺ p q r q≤r)
```

### Addition of a nonnegative rational number is an increasing map

```agda
abstract
  is-inflationary-map-left-add-rational-ℚ⁰⁺ :
    (p : ℚ⁰⁺) → is-inflationary-map-Poset ℚ-Poset (rational-ℚ⁰⁺ p +ℚ_)
  is-inflationary-map-left-add-rational-ℚ⁰⁺ (p , nonneg-p) q =
    tr
      ( λ r → leq-ℚ r (p +ℚ q))
      ( left-unit-law-add-ℚ q)
      ( preserves-leq-left-add-ℚ
        ( q)
        ( zero-ℚ)
        ( p)
        ( leq-zero-is-nonnegative-ℚ p nonneg-p))

  is-inflationary-map-right-add-rational-ℚ⁰⁺ :
    (p : ℚ⁰⁺) → is-inflationary-map-Poset ℚ-Poset (_+ℚ rational-ℚ⁰⁺ p)
  is-inflationary-map-right-add-rational-ℚ⁰⁺ p q =
    tr
      ( leq-ℚ q)
      ( commutative-add-ℚ (rational-ℚ⁰⁺ p) q)
      ( is-inflationary-map-left-add-rational-ℚ⁰⁺ p q)
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

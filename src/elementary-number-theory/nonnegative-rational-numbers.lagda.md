# Nonnegative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.decidable-total-order-rational-numbers
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
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
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
```

## Properties

### The nonnegative rational numbers form a set

```agda
is-set-ℚ⁰⁺ : is-set ℚ⁰⁺
is-set-ℚ⁰⁺ = is-set-type-subtype is-nonnegative-prop-ℚ is-set-ℚ
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
abstract
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

  abstract
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

### The difference of a rational number with a rational number less than or equal to the first is nonnegative

```agda
module _
  (x y : ℚ) (H : leq-ℚ x y)
  where

  abstract
    is-nonnegative-diff-leq-ℚ : is-nonnegative-ℚ (y -ℚ x)
    is-nonnegative-diff-leq-ℚ =
      is-nonnegative-leq-zero-ℚ
        ( y -ℚ x)
        ( backward-implication (iff-translate-diff-leq-zero-ℚ x y) H)

  nonnegative-diff-le-ℚ : ℚ⁰⁺
  nonnegative-diff-le-ℚ = (y -ℚ x , is-nonnegative-diff-leq-ℚ)
```

### The product of two nonnegative rational numbers is nonnegative

```agda
  is-nonnegative-mul-nonnegative-ℚ :
    {x y : ℚ} → is-nonnegative-ℚ x → is-nonnegative-ℚ y →
    is-nonnegative-ℚ (x *ℚ y)
  is-nonnegative-mul-nonnegative-ℚ {x} {y} P Q =
    is-nonnegative-rational-fraction-ℤ
      ( is-nonnegative-mul-nonnegative-fraction-ℤ
        { fraction-ℚ x}
        { fraction-ℚ y}
        ( P)
        ( Q))
```

### Multiplication by a nonnegative rational number preserves inequality

```agda
abstract
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

### Addition on nonnegative rational numbers

```agda
abstract
  is-nonnegative-add-ℚ :
    (p q : ℚ) → is-nonnegative-ℚ p → is-nonnegative-ℚ q →
    is-nonnegative-ℚ (p +ℚ q)
  is-nonnegative-add-ℚ p q nonneg-p nonneg-q =
    is-nonnegative-rational-fraction-ℤ
      ( is-nonnegative-add-fraction-ℤ
        { fraction-ℚ p}
        { fraction-ℚ q}
        ( nonneg-p)
        ( nonneg-q))

add-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
add-ℚ⁰⁺ (p , nonneg-p) (q , nonneg-q) =
  ( p +ℚ q , is-nonnegative-add-ℚ p q nonneg-p nonneg-q)

infixl 35 _+ℚ⁰⁺_
_+ℚ⁰⁺_ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
_+ℚ⁰⁺_ = add-ℚ⁰⁺
```

### Multiplication on nonnegative rational numbers

```agda
abstract
  is-nonnegative-mul-ℚ :
    (p q : ℚ) → is-nonnegative-ℚ p → is-nonnegative-ℚ q →
    is-nonnegative-ℚ (p *ℚ q)
  is-nonnegative-mul-ℚ p q nonneg-p nonneg-q =
    is-nonnegative-rational-fraction-ℤ
      ( is-nonnegative-mul-nonnegative-fraction-ℤ
        { fraction-ℚ p}
        { fraction-ℚ q}
        ( nonneg-p)
        ( nonneg-q))

mul-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
mul-ℚ⁰⁺ (p , nonneg-p) (q , nonneg-q) =
  ( p *ℚ q , is-nonnegative-mul-ℚ p q nonneg-p nonneg-q)

infixl 35 _*ℚ⁰⁺_
_*ℚ⁰⁺_ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
_*ℚ⁰⁺_ = mul-ℚ⁰⁺

abstract
  commutative-mul-ℚ⁰⁺ : (p q : ℚ⁰⁺) → p *ℚ⁰⁺ q ＝ q *ℚ⁰⁺ p
  commutative-mul-ℚ⁰⁺ (p , _) (q , _) = eq-ℚ⁰⁺ (commutative-mul-ℚ p q)
```

### Inequality on nonnegative rational numbers

```agda
leq-ℚ⁰⁺-Prop : ℚ⁰⁺ → ℚ⁰⁺ → Prop lzero
leq-ℚ⁰⁺-Prop (p , _) (q , _) = leq-ℚ-Prop p q

leq-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁺ → UU lzero
leq-ℚ⁰⁺ (p , _) (q , _) = leq-ℚ p q
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

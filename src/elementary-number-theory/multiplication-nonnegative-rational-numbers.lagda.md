# Multiplication of nonnegative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-integer-fractions
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of pairs of nonnegative rational numbers" Agda=mul-ℚ⁰⁺}}
of two
[nonnegative rational numbers](elementary-number-theory.nonnegative-rational-numbers.md)
is their [product](elementary-number-theory.multiplication-rational-numbers.md)
as [rational numbers](elementary-number-theory.rational-numbers.md), and is
itself nonnegative.

## Definition

```agda
opaque
  unfolding mul-ℚ

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
```

## Properties

### Multiplication of nonnegative rational numbers is commutative

```agda
abstract
  commutative-mul-ℚ⁰⁺ : (p q : ℚ⁰⁺) → p *ℚ⁰⁺ q ＝ q *ℚ⁰⁺ p
  commutative-mul-ℚ⁰⁺ (p , _) (q , _) = eq-ℚ⁰⁺ (commutative-mul-ℚ p q)
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

abstract
  preserves-leq-mul-ℚ⁰⁺ :
    (p q r s : ℚ⁰⁺) → leq-ℚ⁰⁺ p q → leq-ℚ⁰⁺ r s → leq-ℚ⁰⁺ (p *ℚ⁰⁺ r) (q *ℚ⁰⁺ s)
  preserves-leq-mul-ℚ⁰⁺ p q r s p≤q r≤s =
    transitive-leq-ℚ
      ( rational-ℚ⁰⁺ (p *ℚ⁰⁺ r))
      ( rational-ℚ⁰⁺ (p *ℚ⁰⁺ s))
      ( rational-ℚ⁰⁺ (q *ℚ⁰⁺ s))
      ( preserves-leq-right-mul-ℚ⁰⁺ s _ _ p≤q)
      ( preserves-leq-left-mul-ℚ⁰⁺ p _ _ r≤s)
```

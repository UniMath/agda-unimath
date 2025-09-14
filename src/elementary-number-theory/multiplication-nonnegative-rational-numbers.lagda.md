# Multiplication of nonnegative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-integer-fractions
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

The
{{#concept "product" WDID=Q40276 WD="multiplication" Disambiguation="of nonnegative rational numbers" Agda=mul-ℚ⁰⁺}}
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

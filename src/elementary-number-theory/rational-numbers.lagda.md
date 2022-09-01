---
title: The rational numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.rational-numbers where

open import elementary-number-theory.divisibility-integers using (div-ℤ)
open import elementary-number-theory.fractions using
  ( fraction-ℤ; numerator-fraction-ℤ; denominator-fraction-ℤ;
    is-positive-denominator-fraction-ℤ)
open import elementary-number-theory.greatest-common-divisor-integers using
  ( gcd-ℤ; is-common-divisor-gcd-ℤ; is-positive-gcd-is-positive-right-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; is-positive-ℤ; is-positive-eq-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; is-positive-left-factor-mul-ℤ)
open import elementary-number-theory.relatively-prime-integers using
  ( is-relative-prime-ℤ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (_＝_; inv)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

The type of rational numbers is the quotient of the type of fractions, by the equivalence relation given by `(n/m) ~ (n'/m') := Id (mul-ℤ n m') (mul-ℤ n' m)`.

```agda
is-reduced-fraction-ℤ : fraction-ℤ → UU lzero
is-reduced-fraction-ℤ x =
  is-relative-prime-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)

ℚ : UU lzero
ℚ = Σ fraction-ℤ is-reduced-fraction-ℤ

reduce-numerator-fraction-ℤ :
  (x : fraction-ℤ) →
  div-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( numerator-fraction-ℤ x)
reduce-numerator-fraction-ℤ x =
  pr1 (is-common-divisor-gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))

int-reduce-numerator-fraction-ℤ : fraction-ℤ → ℤ
int-reduce-numerator-fraction-ℤ x = pr1 (reduce-numerator-fraction-ℤ x)

eq-reduce-numerator-fraction-ℤ :
  (x : fraction-ℤ) →
  ( mul-ℤ
    ( int-reduce-numerator-fraction-ℤ x)
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) ＝
  ( numerator-fraction-ℤ x)
eq-reduce-numerator-fraction-ℤ x = pr2 (reduce-numerator-fraction-ℤ x)

reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  div-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( denominator-fraction-ℤ x)
reduce-denominator-fraction-ℤ x =
  pr2 (is-common-divisor-gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))

int-reduce-denominator-fraction-ℤ : fraction-ℤ → ℤ
int-reduce-denominator-fraction-ℤ x =
  pr1 (reduce-denominator-fraction-ℤ x)

eq-reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  ( mul-ℤ
    ( int-reduce-denominator-fraction-ℤ x)
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) ＝
  ( denominator-fraction-ℤ x)
eq-reduce-denominator-fraction-ℤ x =
  pr2 (reduce-denominator-fraction-ℤ x)

is-positive-int-reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (int-reduce-denominator-fraction-ℤ x)
is-positive-int-reduce-denominator-fraction-ℤ x =
  is-positive-left-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( inv (eq-reduce-denominator-fraction-ℤ x))
      ( is-positive-denominator-fraction-ℤ x))
    ( is-positive-gcd-is-positive-right-ℤ
      ( numerator-fraction-ℤ x)
      ( denominator-fraction-ℤ x)
      ( is-positive-denominator-fraction-ℤ x))

reduce-fraction-ℤ : fraction-ℤ → fraction-ℤ
reduce-fraction-ℤ x =
  pair
    ( int-reduce-numerator-fraction-ℤ x)
    ( pair
      ( int-reduce-denominator-fraction-ℤ x)
      ( is-positive-int-reduce-denominator-fraction-ℤ x))

{-
is-reduced-reduce-fraction-ℤ :
  (x : fraction-ℤ) → is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
is-reduced-reduce-fraction-ℤ x = {!!}
-}
```

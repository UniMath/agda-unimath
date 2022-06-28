---
title: The rational numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.rational-numbers where

open import elementary-number-theory.divisibility-integers using (div-ℤ)
open import elementary-number-theory.fractions using
  ( fractions-ℤ; numerator-fractions-ℤ; denominator-fractions-ℤ;
    is-positive-denominator-fractions-ℤ)
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
is-reduced-fractions-ℤ : fractions-ℤ → UU lzero
is-reduced-fractions-ℤ x =
  is-relative-prime-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x)

ℚ : UU lzero
ℚ = Σ fractions-ℤ is-reduced-fractions-ℤ

reduce-numerator-fractions-ℤ :
  (x : fractions-ℤ) →
  div-ℤ (gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x)) (numerator-fractions-ℤ x)
reduce-numerator-fractions-ℤ x =
  pr1 (is-common-divisor-gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x))

int-reduce-numerator-fractions-ℤ : fractions-ℤ → ℤ
int-reduce-numerator-fractions-ℤ x = pr1 (reduce-numerator-fractions-ℤ x)

eq-reduce-numerator-fractions-ℤ :
  (x : fractions-ℤ) →
  ( mul-ℤ
    ( int-reduce-numerator-fractions-ℤ x)
    ( gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x))) ＝
  ( numerator-fractions-ℤ x)
eq-reduce-numerator-fractions-ℤ x = pr2 (reduce-numerator-fractions-ℤ x)

reduce-denominator-fractions-ℤ :
  (x : fractions-ℤ) →
  div-ℤ (gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x)) (denominator-fractions-ℤ x)
reduce-denominator-fractions-ℤ x =
  pr2 (is-common-divisor-gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x))

int-reduce-denominator-fractions-ℤ : fractions-ℤ → ℤ
int-reduce-denominator-fractions-ℤ x =
  pr1 (reduce-denominator-fractions-ℤ x)

eq-reduce-denominator-fractions-ℤ :
  (x : fractions-ℤ) →
  ( mul-ℤ
    ( int-reduce-denominator-fractions-ℤ x)
    ( gcd-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ x))) ＝
  ( denominator-fractions-ℤ x)
eq-reduce-denominator-fractions-ℤ x =
  pr2 (reduce-denominator-fractions-ℤ x)

is-positive-int-reduce-denominator-fractions-ℤ :
  (x : fractions-ℤ) → is-positive-ℤ (int-reduce-denominator-fractions-ℤ x)
is-positive-int-reduce-denominator-fractions-ℤ x =
  is-positive-left-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( inv (eq-reduce-denominator-fractions-ℤ x))
      ( is-positive-denominator-fractions-ℤ x))
    ( is-positive-gcd-is-positive-right-ℤ
      ( numerator-fractions-ℤ x)
      ( denominator-fractions-ℤ x)
      ( is-positive-denominator-fractions-ℤ x))

reduce-fractions-ℤ : fractions-ℤ → fractions-ℤ
reduce-fractions-ℤ x =
  pair
    ( int-reduce-numerator-fractions-ℤ x)
    ( pair
      ( int-reduce-denominator-fractions-ℤ x)
      ( is-positive-int-reduce-denominator-fractions-ℤ x))

{-
is-reduced-reduce-fractions-ℤ :
  (x : fractions-ℤ) → is-reduced-fractions-ℤ (reduce-fractions-ℤ x)
is-reduced-reduce-fractions-ℤ x = {!!}
-}
```

# The rational numbers

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.rational-numbers where

open import elementary-number-theory.divisibility-integers using (div-ℤ)
open import elementary-number-theory.fractions using
  ( pre-ℚ; numerator-pre-ℚ; denominator-pre-ℚ; is-positive-denominator-pre-ℚ)
open import elementary-number-theory.greatest-common-divisor-integers using
  ( gcd-ℤ; is-common-divisor-gcd-ℤ; is-positive-gcd-is-positive-right-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; is-positive-ℤ; is-positive-eq-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; is-positive-left-factor-mul-ℤ)
open import elementary-number-theory.relatively-prime-integers using
  ( is-relative-prime-ℤ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; inv)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

The type of rational numbers is the quotient of the type of fractions, by the equivalence relation given by `(n/m) ~ (n'/m') := Id (mul-ℤ n m') (mul-ℤ n' m)`.

```agda
is-reduced-pre-ℚ : pre-ℚ → UU lzero
is-reduced-pre-ℚ x =
  is-relative-prime-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)

ℚ : UU lzero
ℚ = Σ pre-ℚ is-reduced-pre-ℚ

reduce-numerator-pre-ℚ :
  (x : pre-ℚ) →
  div-ℤ (gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)) (numerator-pre-ℚ x)
reduce-numerator-pre-ℚ x =
  pr1 (is-common-divisor-gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x))

int-reduce-numerator-pre-ℚ : pre-ℚ → ℤ
int-reduce-numerator-pre-ℚ x = pr1 (reduce-numerator-pre-ℚ x)

eq-reduce-numerator-pre-ℚ :
  (x : pre-ℚ) →
  Id ( mul-ℤ
       ( int-reduce-numerator-pre-ℚ x)
       ( gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)))
     ( numerator-pre-ℚ x)
eq-reduce-numerator-pre-ℚ x = pr2 (reduce-numerator-pre-ℚ x)

reduce-denominator-pre-ℚ :
  (x : pre-ℚ) →
  div-ℤ (gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)) (denominator-pre-ℚ x)
reduce-denominator-pre-ℚ x =
  pr2 (is-common-divisor-gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x))

int-reduce-denominator-pre-ℚ : pre-ℚ → ℤ
int-reduce-denominator-pre-ℚ x =
  pr1 (reduce-denominator-pre-ℚ x)

eq-reduce-denominator-pre-ℚ :
  (x : pre-ℚ) →
  Id ( mul-ℤ
       ( int-reduce-denominator-pre-ℚ x)
       ( gcd-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ x)))
     ( denominator-pre-ℚ x)
eq-reduce-denominator-pre-ℚ x =
  pr2 (reduce-denominator-pre-ℚ x)

is-positive-int-reduce-denominator-pre-ℚ :
  (x : pre-ℚ) → is-positive-ℤ (int-reduce-denominator-pre-ℚ x)
is-positive-int-reduce-denominator-pre-ℚ x =
  is-positive-left-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( inv (eq-reduce-denominator-pre-ℚ x))
      ( is-positive-denominator-pre-ℚ x))
    ( is-positive-gcd-is-positive-right-ℤ
      ( numerator-pre-ℚ x)
      ( denominator-pre-ℚ x)
      ( is-positive-denominator-pre-ℚ x))

reduce-pre-ℚ : pre-ℚ → pre-ℚ
reduce-pre-ℚ x =
  pair
    ( int-reduce-numerator-pre-ℚ x)
    ( pair
      ( int-reduce-denominator-pre-ℚ x)
      ( is-positive-int-reduce-denominator-pre-ℚ x))

{-
is-reduced-reduce-pre-ℚ :
  (x : pre-ℚ) → is-reduced-pre-ℚ (reduce-pre-ℚ x)
is-reduced-reduce-pre-ℚ x = {!!}
-}
```

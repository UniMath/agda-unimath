---
title: The rational numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.rational-numbers where

open import elementary-number-theory.divisibility-integers using
  ( div-ℤ; antisymmetric-div-ℤ; is-plus-or-minus-sim-unit-ℤ;
    div-div-quotient-div-ℤ)
open import elementary-number-theory.equality-integers using
  ( is-decidable-is-one-ℤ; is-decidable-is-zero-ℤ)
open import elementary-number-theory.fractions using
  ( fraction-ℤ; numerator-fraction-ℤ; denominator-fraction-ℤ;
    is-positive-denominator-fraction-ℤ)
open import elementary-number-theory.greatest-common-divisor-integers using
  ( gcd-ℤ; is-common-divisor-gcd-ℤ; is-positive-gcd-is-positive-right-ℤ;
    is-zero-right-is-zero-gcd-ℤ; is-positive-gcd-ℤ; div-gcd-is-common-divisor-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; is-positive-ℤ; is-positive-eq-ℤ; zero-ℤ; one-ℤ; neg-one-ℤ; neg-ℤ;
    is-positive-int-positive-ℤ; is-zero-ℤ; neg-neg-ℤ; is-nonzero-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; is-positive-left-factor-mul-ℤ; is-injective-mul-ℤ'; associative-mul-ℤ;
    commutative-mul-ℤ)
open import elementary-number-theory.relatively-prime-integers using
  ( is-relative-prime-ℤ)

open import foundation.coproduct-types using (ind-coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.functions using (id)
open import foundation.identity-types using (_＝_; inv; tr; refl; ap; _∙_)
open import foundation.negation using (¬)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

The type of rational numbers is the quotient of the type of fractions, by the equivalence relation given by `(n/m) ~ (n'/m') := Id (mul-ℤ n m') (mul-ℤ n' m)`.

## Definitions

### Reduced Fraction

```agda
is-reduced-fraction-ℤ : fraction-ℤ → UU lzero
is-reduced-fraction-ℤ x =
  is-relative-prime-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)
```

### The type of rationals

```agda
ℚ : UU lzero
ℚ = Σ fraction-ℤ is-reduced-fraction-ℤ
```

### Inclusion of the integers

```agda
-- in-int : ℤ → ℚ
-- in-int x =
```

```agda
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
pr1 (reduce-fraction-ℤ x) = int-reduce-numerator-fraction-ℤ x
pr1 (pr2 (reduce-fraction-ℤ x)) = int-reduce-denominator-fraction-ℤ x
pr2 (pr2 (reduce-fraction-ℤ x)) =
  is-positive-int-reduce-denominator-fraction-ℤ x

is-reduced-reduce-fraction-ℤ :
  (x : fraction-ℤ) → is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
is-reduced-reduce-fraction-ℤ x = {!!}

{-
is-reduced-reduce-fraction-ℤ :
  (x : fraction-ℤ) → is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
is-reduced-reduce-fraction-ℤ x with 
  is-decidable-is-zero-ℤ 
    ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
      ( denominator-fraction-ℤ (reduce-fraction-ℤ x)))
is-reduced-reduce-fraction-ℤ x | inl z = ex-falso (tr is-positive-ℤ
        ( is-zero-right-is-zero-gcd-ℤ 
          ( numerator-fraction-ℤ (reduce-fraction-ℤ x))  
          ( denominator-fraction-ℤ (reduce-fraction-ℤ x)) z)
        ( is-positive-denominator-fraction-ℤ (reduce-fraction-ℤ x)))
is-reduced-reduce-fraction-ℤ x | inr nz with
-- do cases on whether alpha * d is plus or minus d
  ( is-plus-or-minus-sim-unit-ℤ
            ( antisymmetric-div-ℤ
              (mul-ℤ 
                ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))) 
                ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)))
              ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
              ( div-gcd-is-common-divisor-ℤ
                ( numerator-fraction-ℤ x)
                ( denominator-fraction-ℤ x)
                (mul-ℤ 
                ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))) 
                ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)))
                ( pair
                  -- alpha * d divides the numerator of x
                  ( tr ( λ - → div-ℤ - (numerator-fraction-ℤ x))
                       ( commutative-mul-ℤ 
                         ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)) 
                         ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))
                       ( div-div-quotient-div-ℤ
                         ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x)))
                         (numerator-fraction-ℤ x)
                         ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
                         ( pr1 ( is-common-divisor-gcd-ℤ
                               ( numerator-fraction-ℤ x)
                               ( denominator-fraction-ℤ x)))
                         ( pr1 ( is-common-divisor-gcd-ℤ
                                 ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
                                 ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))))
                  -- alpha * d divides the denominator of x
                  ( tr ( λ - → div-ℤ - (denominator-fraction-ℤ x))
                       ( commutative-mul-ℤ 
                         ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)) 
                         ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))
                       ( div-div-quotient-div-ℤ
                         ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x)))
                         (denominator-fraction-ℤ x)
                         ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
                         ( pr2 ( is-common-divisor-gcd-ℤ
                               ( numerator-fraction-ℤ x)
                               ( denominator-fraction-ℤ x)))
                         ( pr2 ( is-common-divisor-gcd-ℤ
                                 ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
                                 ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))))))
              (pair ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))) refl)))
is-reduced-reduce-fraction-ℤ x | inr nz | inl pos = ( is-injective-mul-ℤ' 
         ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
           ( λ r →
             tr is-positive-ℤ r
               ( is-positive-gcd-is-positive-right-ℤ
                 ( numerator-fraction-ℤ x)
                 ( denominator-fraction-ℤ x)
                 ( is-positive-denominator-fraction-ℤ x)))) pos
is-reduced-reduce-fraction-ℤ x | inr nz | inr neg =
  ex-falso
    {!!}
{-
  (ex-falso
          ( tr is-positive-ℤ {y = neg-ℤ one-ℤ}
            (inv (neg-neg-ℤ ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
              ( denominator-fraction-ℤ (reduce-fraction-ℤ x)))) ∙
             ap neg-ℤ
               ( is-injective-mul-ℤ' ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
                 ( λ r →
                   tr is-positive-ℤ r
                     ( is-positive-gcd-is-positive-right-ℤ
                       ( numerator-fraction-ℤ x)
                       ( denominator-fraction-ℤ x)
                       ( is-positive-denominator-fraction-ℤ x)))
                 ( associative-mul-ℤ neg-one-ℤ ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
              ( denominator-fraction-ℤ (reduce-fraction-ℤ x))) ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)) ∙ neg)))
            ( is-positive-gcd-ℤ
              ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
              ( denominator-fraction-ℤ (reduce-fraction-ℤ x))
              ( inr
                ( is-positive-denominator-fraction-ℤ
                  (reduce-fraction-ℤ x)))))) 
    ( is-decidable-is-zero-ℤ alpha)
-}
  where
    reduced-fraction : fraction-ℤ
    reduced-fraction = reduce-fraction-ℤ x
    reduced-numerator : ℤ
    reduced-numerator = numerator-fraction-ℤ reduced-fraction
    reduced-denominator : ℤ
    reduced-denominator = denominator-fraction-ℤ reduced-fraction
    d : ℤ
    d = ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    alpha : ℤ
    alpha =
      gcd-ℤ
        ( numerator-fraction-ℤ (reduce-fraction-ℤ x)) 
        ( denominator-fraction-ℤ (reduce-fraction-ℤ x))
        -}
```

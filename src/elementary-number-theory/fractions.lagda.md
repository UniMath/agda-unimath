---
title: Fractions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.fractions where

open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

## Idea

The type of fractions is the type of pairs `n/m` consisting of an integer `n` and a positive integer `m`. The type of rational numbers is a retract of the type of fractions.

## Definition

### The type of fractions of integers

```agda
fraction-ℤ : UU lzero
fraction-ℤ = ℤ × positive-ℤ

numerator-fraction-ℤ : fraction-ℤ → ℤ
numerator-fraction-ℤ x = pr1 x

positive-denominator-fraction-ℤ : fraction-ℤ → positive-ℤ
positive-denominator-fraction-ℤ x = pr2 x

denominator-fraction-ℤ : fraction-ℤ → ℤ
denominator-fraction-ℤ x = pr1 (positive-denominator-fraction-ℤ x)

is-positive-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (denominator-fraction-ℤ x)
is-positive-denominator-fraction-ℤ x = pr2 (positive-denominator-fraction-ℤ x)

is-nonzero-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-nonzero-ℤ (denominator-fraction-ℤ x)
is-nonzero-denominator-fraction-ℤ x =
  is-nonzero-is-positive-ℤ
    ( denominator-fraction-ℤ x)
    ( is-positive-denominator-fraction-ℤ x)
```

### Similarity of fractions of integers

```agda
sim-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
sim-fraction-ℤ-Prop x y =
  Id-Prop ℤ-Set
    (mul-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ y))
    (mul-ℤ (numerator-fraction-ℤ y) (denominator-fraction-ℤ x))

sim-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
sim-fraction-ℤ x y = type-Prop (sim-fraction-ℤ-Prop x y)

is-prop-sim-fraction-ℤ : (x y : fraction-ℤ) → is-prop (sim-fraction-ℤ x y)
is-prop-sim-fraction-ℤ x y = is-prop-type-Prop (sim-fraction-ℤ-Prop x y)

refl-sim-fraction-ℤ : (x : fraction-ℤ) → sim-fraction-ℤ x x
refl-sim-fraction-ℤ x = refl

symm-sim-fraction-ℤ : {x y : fraction-ℤ} → sim-fraction-ℤ x y → sim-fraction-ℤ y x
symm-sim-fraction-ℤ r = inv r

trans-sim-fraction-ℤ :
  {x y z : fraction-ℤ} → sim-fraction-ℤ x y → sim-fraction-ℤ y z → sim-fraction-ℤ x z
trans-sim-fraction-ℤ {x} {y} {z} r s =
  is-injective-mul-ℤ'
    ( denominator-fraction-ℤ y)
    ( is-nonzero-denominator-fraction-ℤ y)
    ( ( associative-mul-ℤ
        ( numerator-fraction-ℤ x)
        ( denominator-fraction-ℤ z)
        ( denominator-fraction-ℤ y)) ∙
      ( ( ap
          ( mul-ℤ (numerator-fraction-ℤ x))
          ( commutative-mul-ℤ
            ( denominator-fraction-ℤ z)
            ( denominator-fraction-ℤ y))) ∙
        ( ( inv
            ( associative-mul-ℤ
              ( numerator-fraction-ℤ x)
              ( denominator-fraction-ℤ y)
              ( denominator-fraction-ℤ z))) ∙
          ( ( ap ( mul-ℤ' (denominator-fraction-ℤ z)) r) ∙
            ( ( associative-mul-ℤ
                ( numerator-fraction-ℤ y)
                ( denominator-fraction-ℤ x)
                ( denominator-fraction-ℤ z)) ∙
              ( ( ap
                  ( mul-ℤ (numerator-fraction-ℤ y))
                  ( commutative-mul-ℤ
                    ( denominator-fraction-ℤ x)
                    ( denominator-fraction-ℤ z))) ∙
                ( ( inv
                    ( associative-mul-ℤ
                      ( numerator-fraction-ℤ y)
                      ( denominator-fraction-ℤ z)
                      ( denominator-fraction-ℤ x))) ∙
                  ( ( ap (mul-ℤ' (denominator-fraction-ℤ x)) s) ∙
                    ( ( associative-mul-ℤ
                        ( numerator-fraction-ℤ z)
                        ( denominator-fraction-ℤ y)
                        ( denominator-fraction-ℤ x)) ∙
                      ( ( ap
                          ( mul-ℤ (numerator-fraction-ℤ z))
                          ( commutative-mul-ℤ
                            ( denominator-fraction-ℤ y)
                            ( denominator-fraction-ℤ x))) ∙
                        ( inv
                          ( associative-mul-ℤ
                            ( numerator-fraction-ℤ z)
                            ( denominator-fraction-ℤ x)
                            ( denominator-fraction-ℤ y)))))))))))))
```

## Properties

### The greatest common divisor of the numerator and a denominator of a fraction is always a positive integer

```agda
is-positive-gcd-numerator-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  is-positive-ℤ (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
is-positive-gcd-numerator-denominator-fraction-ℤ x =
  is-positive-gcd-is-positive-right-ℤ
    ( numerator-fraction-ℤ x)
    ( denominator-fraction-ℤ x)
    ( is-positive-denominator-fraction-ℤ x)

is-nonzero-gcd-numerator-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  is-nonzero-ℤ (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
is-nonzero-gcd-numerator-denominator-fraction-ℤ x =
  is-nonzero-is-positive-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( is-positive-gcd-numerator-denominator-fraction-ℤ x)
```

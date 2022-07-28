---
title: Fractions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.fractions where

open import elementary-number-theory.integers using
  ( ℤ; positive-ℤ; is-positive-ℤ; is-nonzero-ℤ; is-nonzero-is-positive-ℤ;
    ℤ-Set)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; is-injective-mul-ℤ'; associative-mul-ℤ; commutative-mul-ℤ; mul-ℤ')

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (refl; inv; _∙_; ap)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.sets using (Id-Prop)
open import foundation.universe-levels using (UU; lzero)
```

## Idea

The type of fractions is the type of pairs `n/m` consisting of an integer `n` and a positive integer `m`. The type of rational numbers is a retract of the type of fractions.

```agda
fractions-ℤ : UU lzero
fractions-ℤ = ℤ × positive-ℤ

numerator-fractions-ℤ : fractions-ℤ → ℤ
numerator-fractions-ℤ x = pr1 x

positive-denominator-fractions-ℤ : fractions-ℤ → positive-ℤ
positive-denominator-fractions-ℤ x = pr2 x

denominator-fractions-ℤ : fractions-ℤ → ℤ
denominator-fractions-ℤ x = pr1 (positive-denominator-fractions-ℤ x)

is-positive-denominator-fractions-ℤ :
  (x : fractions-ℤ) → is-positive-ℤ (denominator-fractions-ℤ x)
is-positive-denominator-fractions-ℤ x = pr2 (positive-denominator-fractions-ℤ x)

is-nonzero-denominator-fractions-ℤ :
  (x : fractions-ℤ) → is-nonzero-ℤ (denominator-fractions-ℤ x)
is-nonzero-denominator-fractions-ℤ x =
  is-nonzero-is-positive-ℤ
    ( denominator-fractions-ℤ x)
    ( is-positive-denominator-fractions-ℤ x)

sim-fractions-ℤ-Prop : fractions-ℤ → fractions-ℤ → UU-Prop lzero
sim-fractions-ℤ-Prop x y =
  Id-Prop ℤ-Set
    (mul-ℤ (numerator-fractions-ℤ x) (denominator-fractions-ℤ y))
    (mul-ℤ (numerator-fractions-ℤ y) (denominator-fractions-ℤ x))

sim-fractions-ℤ : fractions-ℤ → fractions-ℤ → UU lzero
sim-fractions-ℤ x y = type-Prop (sim-fractions-ℤ-Prop x y)

is-prop-sim-fractions-ℤ : (x y : fractions-ℤ) → is-prop (sim-fractions-ℤ x y)
is-prop-sim-fractions-ℤ x y = is-prop-type-Prop (sim-fractions-ℤ-Prop x y)

refl-sim-fractions-ℤ : (x : fractions-ℤ) → sim-fractions-ℤ x x
refl-sim-fractions-ℤ x = refl

symm-sim-fractions-ℤ : {x y : fractions-ℤ} → sim-fractions-ℤ x y → sim-fractions-ℤ y x
symm-sim-fractions-ℤ r = inv r

trans-sim-fractions-ℤ :
  {x y z : fractions-ℤ} → sim-fractions-ℤ x y → sim-fractions-ℤ y z → sim-fractions-ℤ x z
trans-sim-fractions-ℤ {x} {y} {z} r s =
  is-injective-mul-ℤ'
    ( denominator-fractions-ℤ y)
    ( is-nonzero-denominator-fractions-ℤ y)
    ( ( associative-mul-ℤ
        ( numerator-fractions-ℤ x)
        ( denominator-fractions-ℤ z)
        ( denominator-fractions-ℤ y)) ∙
      ( ( ap
          ( mul-ℤ (numerator-fractions-ℤ x))
          ( commutative-mul-ℤ
            ( denominator-fractions-ℤ z)
            ( denominator-fractions-ℤ y))) ∙
        ( ( inv
            ( associative-mul-ℤ
              ( numerator-fractions-ℤ x)
              ( denominator-fractions-ℤ y)
              ( denominator-fractions-ℤ z))) ∙
          ( ( ap ( mul-ℤ' (denominator-fractions-ℤ z)) r) ∙
            ( ( associative-mul-ℤ
                ( numerator-fractions-ℤ y)
                ( denominator-fractions-ℤ x)
                ( denominator-fractions-ℤ z)) ∙
              ( ( ap
                  ( mul-ℤ (numerator-fractions-ℤ y))
                  ( commutative-mul-ℤ
                    ( denominator-fractions-ℤ x)
                    ( denominator-fractions-ℤ z))) ∙
                ( ( inv
                    ( associative-mul-ℤ
                      ( numerator-fractions-ℤ y)
                      ( denominator-fractions-ℤ z)
                      ( denominator-fractions-ℤ x))) ∙
                  ( ( ap (mul-ℤ' (denominator-fractions-ℤ x)) s) ∙
                    ( ( associative-mul-ℤ
                        ( numerator-fractions-ℤ z)
                        ( denominator-fractions-ℤ y)
                        ( denominator-fractions-ℤ x)) ∙
                      ( ( ap
                          ( mul-ℤ (numerator-fractions-ℤ z))
                          ( commutative-mul-ℤ
                            ( denominator-fractions-ℤ y)
                            ( denominator-fractions-ℤ x))) ∙
                        ( inv
                          ( associative-mul-ℤ
                            ( numerator-fractions-ℤ z)
                            ( denominator-fractions-ℤ x)
                            ( denominator-fractions-ℤ y)))))))))))))
```

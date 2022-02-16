# Fractions

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.fractions where

open import elementary-number-theory.equality-integers using (ℤ-Set)
open import elementary-number-theory.integers using
  ( ℤ; positive-ℤ; is-positive-ℤ; is-nonzero-ℤ; is-nonzero-is-positive-ℤ)
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
pre-ℚ : UU lzero
pre-ℚ = ℤ × positive-ℤ

numerator-pre-ℚ : pre-ℚ → ℤ
numerator-pre-ℚ x = pr1 x

positive-denominator-pre-ℚ : pre-ℚ → positive-ℤ
positive-denominator-pre-ℚ x = pr2 x

denominator-pre-ℚ : pre-ℚ → ℤ
denominator-pre-ℚ x = pr1 (positive-denominator-pre-ℚ x)

is-positive-denominator-pre-ℚ :
  (x : pre-ℚ) → is-positive-ℤ (denominator-pre-ℚ x)
is-positive-denominator-pre-ℚ x = pr2 (positive-denominator-pre-ℚ x)

is-nonzero-denominator-pre-ℚ :
  (x : pre-ℚ) → is-nonzero-ℤ (denominator-pre-ℚ x)
is-nonzero-denominator-pre-ℚ x =
  is-nonzero-is-positive-ℤ
    ( denominator-pre-ℚ x)
    ( is-positive-denominator-pre-ℚ x)

sim-pre-ℚ-Prop : pre-ℚ → pre-ℚ → UU-Prop lzero
sim-pre-ℚ-Prop x y =
  Id-Prop ℤ-Set
    (mul-ℤ (numerator-pre-ℚ x) (denominator-pre-ℚ y))
    (mul-ℤ (numerator-pre-ℚ y) (denominator-pre-ℚ x))

sim-pre-ℚ : pre-ℚ → pre-ℚ → UU lzero
sim-pre-ℚ x y = type-Prop (sim-pre-ℚ-Prop x y)

is-prop-sim-pre-ℚ : (x y : pre-ℚ) → is-prop (sim-pre-ℚ x y)
is-prop-sim-pre-ℚ x y = is-prop-type-Prop (sim-pre-ℚ-Prop x y)

refl-sim-pre-ℚ : (x : pre-ℚ) → sim-pre-ℚ x x
refl-sim-pre-ℚ x = refl

symm-sim-pre-ℚ : {x y : pre-ℚ} → sim-pre-ℚ x y → sim-pre-ℚ y x
symm-sim-pre-ℚ r = inv r

trans-sim-pre-ℚ :
  {x y z : pre-ℚ} → sim-pre-ℚ x y → sim-pre-ℚ y z → sim-pre-ℚ x z
trans-sim-pre-ℚ {x} {y} {z} r s =
  is-injective-mul-ℤ'
    ( denominator-pre-ℚ y)
    ( is-nonzero-denominator-pre-ℚ y)
    ( ( associative-mul-ℤ
        ( numerator-pre-ℚ x)
        ( denominator-pre-ℚ z)
        ( denominator-pre-ℚ y)) ∙
      ( ( ap
          ( mul-ℤ (numerator-pre-ℚ x))
          ( commutative-mul-ℤ
            ( denominator-pre-ℚ z)
            ( denominator-pre-ℚ y))) ∙
        ( ( inv
            ( associative-mul-ℤ
              ( numerator-pre-ℚ x)
              ( denominator-pre-ℚ y)
              ( denominator-pre-ℚ z))) ∙
          ( ( ap ( mul-ℤ' (denominator-pre-ℚ z)) r) ∙
            ( ( associative-mul-ℤ
                ( numerator-pre-ℚ y)
                ( denominator-pre-ℚ x)
                ( denominator-pre-ℚ z)) ∙
              ( ( ap
                  ( mul-ℤ (numerator-pre-ℚ y))
                  ( commutative-mul-ℤ
                    ( denominator-pre-ℚ x)
                    ( denominator-pre-ℚ z))) ∙
                ( ( inv
                    ( associative-mul-ℤ
                      ( numerator-pre-ℚ y)
                      ( denominator-pre-ℚ z)
                      ( denominator-pre-ℚ x))) ∙
                  ( ( ap (mul-ℤ' (denominator-pre-ℚ x)) s) ∙
                    ( ( associative-mul-ℤ
                        ( numerator-pre-ℚ z)
                        ( denominator-pre-ℚ y)
                        ( denominator-pre-ℚ x)) ∙
                      ( ( ap
                          ( mul-ℤ (numerator-pre-ℚ z))
                          ( commutative-mul-ℤ
                            ( denominator-pre-ℚ y)
                            ( denominator-pre-ℚ x))) ∙
                        ( inv
                          ( associative-mul-ℤ
                            ( numerator-pre-ℚ z)
                            ( denominator-pre-ℚ x)
                            ( denominator-pre-ℚ y)))))))))))))
```

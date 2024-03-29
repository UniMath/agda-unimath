# Multiplication on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.interchange-law
```

</details>

## Idea

**Multiplication** on the
[rational numbers](elementary-number-theory.rational-numbers.md) is defined by
extending
[multiplication](elementary-number-theory.multiplication-integer-fractions.md)
on [integer fractions](elementary-number-theory.integer-fractions.md) to the
rational numbers.

## Definition

```agda
mul-ℚ : ℚ → ℚ → ℚ
mul-ℚ (x , p) (y , q) = rational-fraction-ℤ (mul-fraction-ℤ x y)

infixl 40 _*ℚ_
_*ℚ_ = mul-ℚ
```

## Properties

### Unit laws

```agda
left-unit-law-mul-ℚ : (x : ℚ) → one-ℚ *ℚ x ＝ x
left-unit-law-mul-ℚ x =
  ( eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ one-fraction-ℤ (fraction-ℚ x))
    ( fraction-ℚ x)
    ( left-unit-law-mul-fraction-ℤ (fraction-ℚ x))) ∙
  ( is-retraction-rational-fraction-ℚ x)

right-unit-law-mul-ℚ : (x : ℚ) → x *ℚ one-ℚ ＝ x
right-unit-law-mul-ℚ x =
  ( eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ (fraction-ℚ x) one-fraction-ℤ)
    ( fraction-ℚ x)
    ( right-unit-law-mul-fraction-ℤ (fraction-ℚ x))) ∙
  ( is-retraction-rational-fraction-ℚ x)
```

### Negative unit laws

```agda
left-neg-unit-law-mul-ℚ : (x : ℚ) → neg-one-ℚ *ℚ x ＝ neg-ℚ x
left-neg-unit-law-mul-ℚ x =
  eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ (fraction-ℚ neg-one-ℚ) (fraction-ℚ x))
    ( neg-fraction-ℤ (fraction-ℚ x))
    ( ap-mul-ℤ
      ( left-neg-unit-law-mul-ℤ (numerator-ℚ x))
      ( inv (left-unit-law-mul-ℤ (denominator-ℚ x)))) ∙
  ( is-retraction-rational-fraction-ℚ (neg-ℚ x))

right-neg-unit-law-mul-ℚ : (x : ℚ) → x *ℚ neg-one-ℚ ＝ neg-ℚ x
right-neg-unit-law-mul-ℚ x =
  eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ neg-one-ℚ))
    ( neg-fraction-ℤ (fraction-ℚ x))
    ( ap-mul-ℤ
      ( right-neg-unit-law-mul-ℤ (numerator-ℚ x))
      ( inv (right-unit-law-mul-ℤ (denominator-ℚ x)))) ∙
  ( is-retraction-rational-fraction-ℚ (neg-ℚ x))
```

### Multiplication of rational numbers is associative

```agda
associative-mul-ℚ :
  (x y z : ℚ) → (x *ℚ y) *ℚ z ＝ x *ℚ (y *ℚ z)
associative-mul-ℚ x y z =
  eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ z))
    ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y *ℚ z)))
    ( transitive-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ z))
      ( mul-fraction-ℤ
        ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
        ( fraction-ℚ z))
      ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y *ℚ z)))
      ( transitive-sim-fraction-ℤ
        ( mul-fraction-ℤ
          ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
          ( fraction-ℚ z))
        ( mul-fraction-ℤ
          ( fraction-ℚ x)
          ( mul-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
        ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y *ℚ z)))
        ( sim-fraction-mul-fraction-ℤ
          ( refl-sim-fraction-ℤ (fraction-ℚ x))
          ( sim-reduced-fraction-ℤ
            ( mul-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z))))
        ( associative-mul-fraction-ℤ
          ( fraction-ℚ x)
          ( fraction-ℚ y)
          ( fraction-ℚ z)))
      ( sim-fraction-mul-fraction-ℤ
        ( inv
          ( sim-reduced-fraction-ℤ
            ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
        ( refl-sim-fraction-ℤ (fraction-ℚ z))))
```

### Multiplication of rational numbers is commutative

```agda
commutative-mul-ℚ : (x y : ℚ) → x *ℚ y ＝ y *ℚ x
commutative-mul-ℚ x y =
  eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
    ( mul-fraction-ℤ (fraction-ℚ y) (fraction-ℚ x))
    ( commutative-mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
```

### Interchange law

```agda
interchange-law-mul-mul-ℚ :
  (x y u v : ℚ) → (x *ℚ y) *ℚ (u *ℚ v) ＝ (x *ℚ u) *ℚ (y *ℚ v)
interchange-law-mul-mul-ℚ =
  interchange-law-commutative-and-associative
    mul-ℚ
    commutative-mul-ℚ
    associative-mul-ℚ
```

### Negative laws

```agda
module _
  (x y : ℚ)
  where

  left-negative-law-mul-ℚ : (neg-ℚ x) *ℚ y ＝ neg-ℚ (x *ℚ y)
  left-negative-law-mul-ℚ =
    ( ap ( _*ℚ y) (inv (left-neg-unit-law-mul-ℚ x))) ∙
    ( associative-mul-ℚ neg-one-ℚ x y) ∙
    ( left-neg-unit-law-mul-ℚ (x *ℚ y))

  right-negative-law-mul-ℚ : x *ℚ (neg-ℚ y) ＝ neg-ℚ (x *ℚ y)
  right-negative-law-mul-ℚ =
    ( ap ( x *ℚ_) (inv (right-neg-unit-law-mul-ℚ y))) ∙
    ( inv (associative-mul-ℚ x y neg-one-ℚ)) ∙
    ( right-neg-unit-law-mul-ℚ (x *ℚ y))

negative-law-mul-ℚ : (x y : ℚ) → (neg-ℚ x) *ℚ (neg-ℚ y) ＝ x *ℚ y
negative-law-mul-ℚ x y =
  ( left-negative-law-mul-ℚ x (neg-ℚ y)) ∙
  ( ap neg-ℚ (right-negative-law-mul-ℚ x y)) ∙
  ( neg-neg-ℚ (x *ℚ y))
```

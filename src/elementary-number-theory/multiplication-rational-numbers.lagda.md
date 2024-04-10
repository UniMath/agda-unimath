# Multiplication on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
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

mul-ℚ' : ℚ → ℚ → ℚ
mul-ℚ' x y = mul-ℚ y x

infixl 40 _*ℚ_
_*ℚ_ = mul-ℚ
```

## Properties

### The multiplication of a rational number by zero is zero

```agda
module _
  (x : ℚ)
  where

  left-zero-law-mul-ℚ : zero-ℚ *ℚ x ＝ zero-ℚ
  left-zero-law-mul-ℚ =
    ( eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ zero-ℚ) (fraction-ℚ x))
      ( fraction-ℚ zero-ℚ)
      ( eq-is-zero-ℤ
        ( ap (mul-ℤ' one-ℤ) (left-zero-law-mul-ℤ (numerator-ℚ x)))
        ( left-zero-law-mul-ℤ _))) ∙
    ( is-retraction-rational-fraction-ℚ zero-ℚ)

  right-zero-law-mul-ℚ : x *ℚ zero-ℚ ＝ zero-ℚ
  right-zero-law-mul-ℚ =
    ( eq-ℚ-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ zero-ℚ))
      ( fraction-ℚ zero-ℚ)
      ( eq-is-zero-ℤ
        ( ap (mul-ℤ' one-ℤ) (right-zero-law-mul-ℤ (numerator-ℚ x)))
        ( left-zero-law-mul-ℤ _))) ∙
    ( is-retraction-rational-fraction-ℚ zero-ℚ)
```

### If the product of two rational numbers is zero, the left or right factor is zero

```agda
decide-is-zero-factor-is-zero-mul-ℚ :
  (x y : ℚ) → is-zero-ℚ (x *ℚ y) → (is-zero-ℚ x) + (is-zero-ℚ y)
decide-is-zero-factor-is-zero-mul-ℚ x y H =
  rec-coproduct
    ( inl ∘ is-zero-is-zero-numerator-ℚ x)
    ( inr ∘ is-zero-is-zero-numerator-ℚ y)
    ( is-zero-is-zero-mul-ℤ
      ( numerator-ℚ x)
      ( numerator-ℚ y)
      ( ( inv
          ( eq-reduce-numerator-fraction-ℤ
            ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))) ∙
        ( ap
          ( mul-ℤ'
            ( gcd-ℤ
              ( numerator-ℚ x *ℤ numerator-ℚ y)
              ( denominator-ℚ x *ℤ denominator-ℚ y)))
          ( ( is-zero-numerator-is-zero-ℚ (x *ℚ y) H) ∙
            ( left-zero-law-mul-ℤ
              ( gcd-ℤ
                (numerator-ℚ x *ℤ numerator-ℚ y)
                (denominator-ℚ x *ℤ denominator-ℚ y)))))))
```

### Unit laws for multiplication on rational numbers

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

### Multiplication of a rational number by `-1` is equal to the negative

```agda
left-neg-unit-law-mul-ℚ : (x : ℚ) → neg-one-ℚ *ℚ x ＝ neg-ℚ x
left-neg-unit-law-mul-ℚ x =
  ( eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ (fraction-ℚ neg-one-ℚ) (fraction-ℚ x))
    ( neg-fraction-ℤ (fraction-ℚ x))
    ( ap-mul-ℤ
      ( left-neg-unit-law-mul-ℤ (numerator-ℚ x))
      ( inv (left-unit-law-mul-ℤ (denominator-ℚ x))))) ∙
  ( is-retraction-rational-fraction-ℚ (neg-ℚ x))

right-neg-unit-law-mul-ℚ : (x : ℚ) → x *ℚ neg-one-ℚ ＝ neg-ℚ x
right-neg-unit-law-mul-ℚ x =
  ( eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ neg-one-ℚ))
    ( neg-fraction-ℤ (fraction-ℚ x))
    ( ap-mul-ℤ
      ( right-neg-unit-law-mul-ℤ (numerator-ℚ x))
      ( inv (right-unit-law-mul-ℤ (denominator-ℚ x))))) ∙
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

### Interchange law for multiplication on rational numbers with itself

```agda
interchange-law-mul-mul-ℚ :
  (x y u v : ℚ) → (x *ℚ y) *ℚ (u *ℚ v) ＝ (x *ℚ u) *ℚ (y *ℚ v)
interchange-law-mul-mul-ℚ =
  interchange-law-commutative-and-associative
    mul-ℚ
    commutative-mul-ℚ
    associative-mul-ℚ
```

### Negative laws for multiplication on rational numbers

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

swap-neg-mul-ℚ : (x y : ℚ) → x *ℚ (neg-ℚ y) ＝ (neg-ℚ x) *ℚ y
swap-neg-mul-ℚ x y =
  ( right-negative-law-mul-ℚ x y) ∙
  ( inv (left-negative-law-mul-ℚ x y))
```

### Multiplication on rational numbers distributes over addition

```agda
left-distributive-mul-add-ℚ :
  (x y z : ℚ) → x *ℚ (y +ℚ z) ＝ (x *ℚ y) +ℚ (x *ℚ z)
left-distributive-mul-add-ℚ x y z =
  eq-ℚ-sim-fraction-ℤ
    ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y +ℚ z)))
    ( add-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ (x *ℚ z)))
    ( transitive-sim-fraction-ℤ
      ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ (y +ℚ z)))
      ( mul-fraction-ℤ
        ( fraction-ℚ x)
        ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
      ( add-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ (x *ℚ z)))
      ( transitive-sim-fraction-ℤ
        ( mul-fraction-ℤ
          ( fraction-ℚ x)
          ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
        ( add-fraction-ℤ
          ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
          ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ z)))
        ( add-fraction-ℤ (fraction-ℚ (x *ℚ y)) (fraction-ℚ (x *ℚ z)))
        ( sim-fraction-add-fraction-ℤ
          ( sim-reduced-fraction-ℤ
            ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
          ( sim-reduced-fraction-ℤ
            ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ z))))
        ( left-distributive-mul-add-fraction-ℤ
          ( fraction-ℚ x)
          ( fraction-ℚ y)
          ( fraction-ℚ z)))
      ( sim-fraction-mul-fraction-ℤ
        ( refl-sim-fraction-ℤ (fraction-ℚ x))
        ( transitive-sim-fraction-ℤ
          ( fraction-ℚ (y +ℚ z))
          ( reduce-fraction-ℤ (add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
          ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z))
          ( symmetric-sim-fraction-ℤ
            ( add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z))
            ( reduce-fraction-ℤ (add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z)))
            ( sim-reduced-fraction-ℤ
              (add-fraction-ℤ (fraction-ℚ y) (fraction-ℚ z))))
          ( refl-sim-fraction-ℤ (fraction-ℚ (y +ℚ z))))))

right-distributive-mul-add-ℚ :
  (x y z : ℚ) → (x +ℚ y) *ℚ z ＝ (x *ℚ z) +ℚ (y *ℚ z)
right-distributive-mul-add-ℚ x y z =
  ( commutative-mul-ℚ (x +ℚ y) z) ∙
  ( left-distributive-mul-add-ℚ z x y) ∙
  ( ap-add-ℚ (commutative-mul-ℚ z x) (commutative-mul-ℚ z y))
```

### Multiplication on rational numbers distributes over the difference

```agda
left-distributive-mul-diff-ℚ :
  (z x y : ℚ) → z *ℚ (x -ℚ y) ＝ (z *ℚ x) -ℚ (z *ℚ y)
left-distributive-mul-diff-ℚ z x y =
  ( left-distributive-mul-add-ℚ z x (neg-ℚ y)) ∙
  ( ap ((z *ℚ x) +ℚ_) (right-negative-law-mul-ℚ z y))

right-distributive-mul-diff-ℚ :
  (x y z : ℚ) → (x -ℚ y) *ℚ z ＝ (x *ℚ z) -ℚ (y *ℚ z)
right-distributive-mul-diff-ℚ x y z =
  ( right-distributive-mul-add-ℚ x (neg-ℚ y) z) ∙
  ( ap ((x *ℚ z) +ℚ_) (left-negative-law-mul-ℚ y z))
```

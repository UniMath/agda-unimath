# Addition on the rationals

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.addition-rationals where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
```

</details>

## Idea

We introduce addition on the rationals and derive its basic properties.
Properties of addition with respect to inequality are derived in
`inequality-rationals`.

## Definition

```agda
add-ℚ : ℚ → ℚ → ℚ
add-ℚ (x , p) (y , q) = in-fraction-ℤ (add-fraction-ℤ x y)

add-ℚ' : ℚ → ℚ → ℚ
add-ℚ' x y = add-ℚ y x

infix 30 _+ℚ_
_+ℚ_ = add-ℚ

ap-add-ℚ :
  {x y x' y' : ℚ} → x ＝ x' → y ＝ y' → add-ℚ x y ＝ add-ℚ x' y'
ap-add-ℚ p q = ap-binary add-ℚ p q
```

## Properties

### Unit laws

```agda
left-unit-law-add-ℚ : (x : ℚ) → zero-ℚ +ℚ x ＝ x
left-unit-law-add-ℚ (x , p) =
  eq-ℚ-sim-fractions-ℤ
    ( add-fraction-ℤ zero-fraction-ℤ x)
    ( x)
    ( left-unit-law-add-fraction-ℤ x) ∙
  in-fraction-fraction-ℚ (x , p)

right-unit-law-add-ℚ : (x : ℚ) → x +ℚ zero-ℚ ＝ x
right-unit-law-add-ℚ (x , p) =
  eq-ℚ-sim-fractions-ℤ
    ( add-fraction-ℤ x zero-fraction-ℤ)
    ( x)
    ( right-unit-law-add-fraction-ℤ x) ∙
  in-fraction-fraction-ℚ (x , p)
```

### Addition is commutative

```agda
commutative-add-ℚ :
  (x y  : ℚ) →
  x +ℚ y ＝ y +ℚ x
commutative-add-ℚ (x , px) (y , py) =
  eq-ℚ-sim-fractions-ℤ
    ( add-fraction-ℤ x y)
    ( add-fraction-ℤ y x)
    ( commutative-add-fraction-ℤ x y)
```

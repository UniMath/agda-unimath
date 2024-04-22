# The multiplicative group of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplicative-group-of-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractions
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.submonoids
```

</details>

## Idea

The [submonoid](group-theory.submonoids.md) of
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
in the
[multiplicative monoid of rational numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md)
is a [commutative group](group-theory.abelian-groups.md).

## Lemma

### The positive rational numbers are invertible

```agda
module _
  (x : ℚ) (P : is-positive-ℚ x)
  where

  inv-is-positive-ℚ : ℚ
  pr1 inv-is-positive-ℚ = inv-is-positive-fraction-ℤ (fraction-ℚ x) P
  pr2 inv-is-positive-ℚ =
    is-reduced-inv-is-positive-fraction-ℤ
      ( fraction-ℚ x)
      ( P)
      ( is-reduced-fraction-ℚ x)

  abstract
    left-inverse-law-mul-is-positive-ℚ : inv-is-positive-ℚ *ℚ x ＝ one-ℚ
    left-inverse-law-mul-is-positive-ℚ =
      ( eq-ℚ-sim-fraction-ℤ
        ( mul-fraction-ℤ
          ( inv-is-positive-fraction-ℤ (fraction-ℚ x) P)
          ( fraction-ℚ x))
        ( one-fraction-ℤ)
        ( left-inverse-law-mul-is-positive-fraction-ℤ (fraction-ℚ x) P)) ∙
      ( is-retraction-rational-fraction-ℚ one-ℚ)

    right-inverse-law-mul-is-positive-ℚ : x *ℚ inv-is-positive-ℚ ＝ one-ℚ
    right-inverse-law-mul-is-positive-ℚ =
      (commutative-mul-ℚ x _) ∙ (left-inverse-law-mul-is-positive-ℚ)

  is-invertible-is-positive-ℚ : is-invertible-element-Monoid ℚ-mul-Monoid x
  pr1 is-invertible-is-positive-ℚ = inv-is-positive-ℚ
  pr1 (pr2 is-invertible-is-positive-ℚ) = right-inverse-law-mul-is-positive-ℚ
  pr2 (pr2 is-invertible-is-positive-ℚ) = left-inverse-law-mul-is-positive-ℚ
```

## Definitions

### The positive inverse of a positive rational number

```agda
inv-ℚ⁺ : ℚ⁺ → ℚ⁺
pr1 (inv-ℚ⁺ (x , P)) = inv-is-positive-ℚ x P
pr2 (inv-ℚ⁺ (x , P)) = is-positive-denominator-ℚ x
```

### The multiplicative group of positive rational numbers

```agda
ℚ⁺-mul-Group : Group lzero
pr1 ℚ⁺-mul-Group = semigroup-Submonoid ℚ-mul-Monoid ℚ⁺-mul-Submonoid
pr1 (pr2 ℚ⁺-mul-Group) = is-unital-Monoid ℚ⁺-mul-Monoid
pr1 (pr2 (pr2 ℚ⁺-mul-Group)) = inv-ℚ⁺
pr1 (pr2 (pr2 (pr2 ℚ⁺-mul-Group))) x =
  eq-ℚ⁺
    ( left-inverse-law-mul-is-positive-ℚ
      ( rational-ℚ⁺ x)
      ( is-positive-rational-ℚ⁺ x))
pr2 (pr2 (pr2 (pr2 ℚ⁺-mul-Group))) x =
  eq-ℚ⁺
    ( right-inverse-law-mul-is-positive-ℚ
      ( rational-ℚ⁺ x)
      ( is-positive-rational-ℚ⁺ x))
```

## Properties

### The multiplicative group of positive rational numbers is commutative

```agda
ℚ⁺-mul-Ab : Ab lzero
pr1 ℚ⁺-mul-Ab = ℚ⁺-mul-Group
pr2 ℚ⁺-mul-Ab x y = eq-ℚ⁺ (commutative-mul-ℚ (rational-ℚ⁺ x) (rational-ℚ⁺ y))
```

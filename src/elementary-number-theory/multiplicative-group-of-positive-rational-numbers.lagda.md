# The multiplicative group of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplicative-group-of-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
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

## Definitions

### The positive inverse of a positive rational number

```agda
inv-ℚ⁺ : ℚ⁺ → ℚ⁺
pr1 (inv-ℚ⁺ (x , P)) = inv-is-positive-ℚ x P
pr2 (inv-ℚ⁺ (x , P)) = is-positive-denominator-ℚ x
```

### The multiplicative group of positive rational numbers

```agda
group-mul-ℚ⁺ : Group lzero
pr1 group-mul-ℚ⁺ = semigroup-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺
pr1 (pr2 group-mul-ℚ⁺) = is-unital-Monoid monoid-mul-ℚ⁺
pr1 (pr2 (pr2 group-mul-ℚ⁺)) = inv-ℚ⁺
pr1 (pr2 (pr2 (pr2 group-mul-ℚ⁺))) x =
  eq-ℚ⁺
    ( left-inverse-law-mul-is-positive-ℚ
      ( rational-ℚ⁺ x)
      ( is-positive-rational-ℚ⁺ x))
pr2 (pr2 (pr2 (pr2 group-mul-ℚ⁺))) x =
  eq-ℚ⁺
    ( right-inverse-law-mul-is-positive-ℚ
      ( rational-ℚ⁺ x)
      ( is-positive-rational-ℚ⁺ x))
```

### Inverse laws in the multiplicative group of positive rational numbers

```agda
left-inverse-law-mul-ℚ⁺ : (x : ℚ⁺) → (inv-ℚ⁺ x) *ℚ⁺ x ＝ one-ℚ⁺
left-inverse-law-mul-ℚ⁺ = left-inverse-law-mul-Group group-mul-ℚ⁺

right-inverse-law-mul-ℚ⁺ : (x : ℚ⁺) → x *ℚ⁺ (inv-ℚ⁺ x) ＝ one-ℚ⁺
right-inverse-law-mul-ℚ⁺ = right-inverse-law-mul-Group group-mul-ℚ⁺
```

## Properties

### The multiplicative group of positive rational numbers is commutative

```agda
abelian-group-mul-ℚ⁺ : Ab lzero
pr1 abelian-group-mul-ℚ⁺ = group-mul-ℚ⁺
pr2 abelian-group-mul-ℚ⁺ = commutative-mul-ℚ⁺
```

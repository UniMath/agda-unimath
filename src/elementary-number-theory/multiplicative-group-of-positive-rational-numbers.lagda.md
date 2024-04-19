# The multiplicative group of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplicative-group-of-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-inverses-positive-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.submonoids
```

</details>

## Idea

The submonoid of
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
in the
[multiplicative monoid of rational numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md)
is a [commutative group](group-theory.abelian-groups.md).

## Definitions

### The positive inverse of a positive rational number

```agda
inv-ℚ⁺ : ℚ⁺ → ℚ⁺
pr1 (inv-ℚ⁺ (x , P)) = inv-is-positive-ℚ {x} P
pr2 (inv-ℚ⁺ (x , P)) = is-positive-denominator-ℚ x
```

### The multiplicative group of positive rational numbers

```agda
ℚ⁺-mul-Group : Group lzero
pr1 ℚ⁺-mul-Group = semigroup-Submonoid ℚ-mul-Monoid ℚ⁺-mul-Submonoid
pr1 (pr2 ℚ⁺-mul-Group) = is-unital-Monoid (monoid-Submonoid _ _)
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
pr2 ℚ⁺-mul-Ab x y =
  eq-ℚ⁺ (commutative-mul-ℚ (rational-ℚ⁺ x) (rational-ℚ⁺ y))
```

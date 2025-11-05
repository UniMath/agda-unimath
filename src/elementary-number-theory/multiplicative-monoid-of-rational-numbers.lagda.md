# The multiplicative monoid of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplicative-monoid-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a [commutative monoid](group-theory.commutative-monoids.md) with unit `one-ℚ`.

## Definitions

### The multiplicative monoid of rational numbers

```agda
semigroup-mul-ℚ : Semigroup lzero
pr1 semigroup-mul-ℚ = ℚ-Set
pr1 (pr2 semigroup-mul-ℚ) = mul-ℚ
pr2 (pr2 semigroup-mul-ℚ) = associative-mul-ℚ

is-unital-mul-ℚ : is-unital mul-ℚ
pr1 is-unital-mul-ℚ = one-ℚ
pr1 (pr2 is-unital-mul-ℚ) = left-unit-law-mul-ℚ
pr2 (pr2 is-unital-mul-ℚ) = right-unit-law-mul-ℚ

monoid-mul-ℚ : Monoid lzero
pr1 monoid-mul-ℚ = semigroup-mul-ℚ
pr2 monoid-mul-ℚ = is-unital-mul-ℚ
```

## Properties

### The multiplicative monoid of rational numbers is commutative

```agda
commutative-monoid-mul-ℚ : Commutative-Monoid lzero
pr1 commutative-monoid-mul-ℚ = monoid-mul-ℚ
pr2 commutative-monoid-mul-ℚ = commutative-mul-ℚ
```

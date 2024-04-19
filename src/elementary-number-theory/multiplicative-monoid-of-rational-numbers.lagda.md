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
[multiplication](elementary-number-theory.addition-rational-numbers.md) is a
[commutative monoid](group-theory.commutative-monoids.md) with unit `one-ℚ`.

## Definitions

### The multiplicative monoid of rational numbers

```agda
ℚ-mul-Semigroup : Semigroup lzero
pr1 ℚ-mul-Semigroup = ℚ-Set
pr1 (pr2 ℚ-mul-Semigroup) = mul-ℚ
pr2 (pr2 ℚ-mul-Semigroup) = associative-mul-ℚ

is-unital-mul-ℚ : is-unital mul-ℚ
pr1 is-unital-mul-ℚ = one-ℚ
pr1 (pr2 is-unital-mul-ℚ) = left-unit-law-mul-ℚ
pr2 (pr2 is-unital-mul-ℚ) = right-unit-law-mul-ℚ

ℚ-mul-Monoid : Monoid lzero
pr1 ℚ-mul-Monoid = ℚ-mul-Semigroup
pr2 ℚ-mul-Monoid = is-unital-mul-ℚ
```

## Properties

### The multiplicative monoid of rational numbers is commutative

```agda
ℚ-mul-Commutative-Monoid : Commutative-Monoid lzero
pr1 ℚ-mul-Commutative-Monoid = ℚ-mul-Monoid
pr2 ℚ-mul-Commutative-Monoid = commutative-mul-ℚ
```

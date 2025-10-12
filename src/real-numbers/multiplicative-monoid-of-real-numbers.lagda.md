# The multiplicative monoid of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplicative-monoid-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The [real numbers](real-numbers.dedekind-real-numbers.md) form a
[commutative monoid](group-theory.commutative-monoids.md) under
[multiplication](real-numbers.multiplication-real-numbers.md).

## Definition

```agda
semigroup-mul-ℝ-lzero : Semigroup (lsuc lzero)
semigroup-mul-ℝ-lzero =
  ( ℝ-Set lzero ,
    mul-ℝ ,
    associative-mul-ℝ)

monoid-mul-ℝ-lzero : Monoid (lsuc lzero)
monoid-mul-ℝ-lzero =
  ( semigroup-mul-ℝ-lzero ,
    one-ℝ ,
    left-unit-law-mul-ℝ ,
    right-unit-law-mul-ℝ)

commutative-monoid-mul-ℝ-lzero : Commutative-Monoid (lsuc lzero)
commutative-monoid-mul-ℝ-lzero =
  ( monoid-mul-ℝ-lzero ,
    commutative-mul-ℝ)
```

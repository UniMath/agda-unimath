# The multiplicative monoid of nonnegative rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplicative-monoid-of-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.submonoids-commutative-monoids
```

</details>

## Idea

The type of
[nonnegative](elementary-number-theory.nonnegative-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md) equipped with
[multiplication](elementary-number-theory.multiplication-nonnegative-rational-numbers.md)
is a [commutative monoid](group-theory.commutative-monoids.md) with unit
`one-ℚ⁰⁺`.

## Definitions

### The multiplicative commutative monoid of nonnegative rational numbers

```agda
nonnegative-submonoid-commutative-monoid-mul-ℚ :
  Commutative-Submonoid lzero commutative-monoid-mul-ℚ
nonnegative-submonoid-commutative-monoid-mul-ℚ =
  ( is-nonnegative-prop-ℚ ,
    is-nonnegative-one-ℚ ,
    λ _ _ → is-nonnegative-mul-ℚ)

commutative-monoid-mul-ℚ⁰⁺ : Commutative-Monoid lzero
commutative-monoid-mul-ℚ⁰⁺ =
  commutative-monoid-Commutative-Submonoid
    ( commutative-monoid-mul-ℚ)
    ( nonnegative-submonoid-commutative-monoid-mul-ℚ)

monoid-mul-ℚ⁰⁺ : Monoid lzero
monoid-mul-ℚ⁰⁺ = monoid-Commutative-Monoid commutative-monoid-mul-ℚ⁰⁺
```

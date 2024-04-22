# The multiplicative group of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplicative-group-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.discrete-field-of-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.cores-monoids
open import group-theory.groups
open import group-theory.submonoids-commutative-monoids

open import ring-theory.groups-of-units-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.trivial-rings
```

</details>

## Idea

The multiplicative group of rational numbers is the
[group of units](ring-theory.groups-of-units-rings.md) of the
[ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md),
the [core](group-theory.cores-monoids.md) of the
[multiplicative monoid of rational numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md).

## Definitions

### The multiplicative group of rational numbers

```agda
group-of-units-ℚ : Group lzero
group-of-units-ℚ = group-of-units-Ring ring-ℚ

group-mul-ℚˣ : Group lzero
group-mul-ℚˣ = group-of-units-Ring ring-ℚ
```

### The type of invertible rational numbers

```agda
ℚˣ : UU lzero
ℚˣ = type-group-of-units-Ring ring-ℚ
```

### Operations of the multiplicative group of rational numbers

```agda
mul-ℚˣ : ℚˣ → ℚˣ → ℚˣ
mul-ℚˣ = mul-group-of-units-Ring ring-ℚ

infixl 40 _*ℚˣ_
_*ℚˣ_ = mul-ℚˣ

inv-ℚˣ : ℚˣ → ℚˣ
inv-ℚˣ = inv-group-of-units-Ring ring-ℚ
```

## Properties

### The multiplicative group of rational numbers is commutative

```agda
commutative-mul-ℚˣ : (x y : ℚˣ) → (x *ℚˣ y) ＝ (y *ℚˣ x)
commutative-mul-ℚˣ =
  commutative-mul-Commutative-Submonoid
    ( commutative-monoid-mul-ℚ)
    ( submonoid-core-Monoid monoid-mul-ℚ)

abelian-group-mul-ℚˣ : Ab lzero
pr1 abelian-group-mul-ℚˣ = group-mul-ℚˣ
pr2 abelian-group-mul-ℚˣ = commutative-mul-ℚˣ
```

### The elements of the multiplicative group of the rational numbers are the nonzero rational numbers

```agda
module _
  (x : ℚ)
  where

  is-nonzero-is-invertible-ℚ :
    is-invertible-element-Ring ring-ℚ x → is-nonzero-ℚ x
  is-nonzero-is-invertible-ℚ H K =
    is-nonzero-is-invertible-element-nontrivial-Ring
      ( ring-ℚ)
      ( pr1 is-division-ring-ℚ)
      ( x)
      ( H)
      ( inv K)

  is-invertible-is-nonzero-ℚ :
    is-nonzero-ℚ x → is-invertible-element-Ring ring-ℚ x
  is-invertible-is-nonzero-ℚ = is-invertible-element-ring-is-nonzero-ℚ x

eq-is-invertible-prop-is-nonzero-prop-ℚ :
  is-nonzero-prop-ℚ ＝ is-invertible-element-prop-Ring ring-ℚ
eq-is-invertible-prop-is-nonzero-prop-ℚ =
  antisymmetric-leq-subtype
    ( is-nonzero-prop-ℚ)
    ( is-invertible-element-prop-Ring ring-ℚ)
    ( is-invertible-is-nonzero-ℚ)
    ( is-nonzero-is-invertible-ℚ)
```

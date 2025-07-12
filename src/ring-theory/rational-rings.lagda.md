# Rational rings

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.rational-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.localizations-rings
open import ring-theory.rings
```

</details>

## Idea

A {{#concept "rational ring" Agda=Rational-Ring}} is a
[ring](ring-theory.rings.md) where the
[positive integers](elementary-number-theory.positive-integers.md) are
[invertible](ring-theory.invertible-elements-rings.md) (modulo the
[initial ring morphism](elementary-number-theory.ring-of-integers.md)).

The
[ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md)
is the [initial](ring-theory.inital-rings.md) rational ring.

## Definitions

### The property of being a rational ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-prop-Ring : Prop l
  is-rational-prop-Ring =
    inverts-subset-prop-hom-Ring
      ( ℤ-Ring)
      ( R)
      ( subtype-positive-ℤ)
      ( initial-hom-Ring R)

  is-rational-Ring : UU l
  is-rational-Ring = type-Prop is-rational-prop-Ring

  is-prop-is-rational-Ring : is-prop is-rational-Ring
  is-prop-is-rational-Ring = is-prop-type-Prop is-rational-prop-Ring
```

### The type of rational rings

```agda
Rational-Ring : (l : Level) → UU (lsuc l)
Rational-Ring l = Σ (Ring l) is-rational-Ring

module _
  {l : Level} (R : Rational-Ring l)
  where

  ring-Rational-Ring : Ring l
  ring-Rational-Ring = pr1 R

  type-Rational-Ring : UU l
  type-Rational-Ring = type-Ring ring-Rational-Ring

  is-rational-ring-Rational-Ring : is-rational-Ring ring-Rational-Ring
  is-rational-ring-Rational-Ring = pr2 R

  inv-positive-integer-Rational-Ring : ℤ⁺ → type-Rational-Ring
  inv-positive-integer-Rational-Ring (k , k>0) =
    inv-is-invertible-element-Ring
      ( ring-Rational-Ring)
      ( is-rational-ring-Rational-Ring k k>0)

  left-inverse-law-positive-integer-Rational-Ring :
    (k : ℤ⁺) →
    mul-Ring
      ( ring-Rational-Ring)
      ( inv-positive-integer-Rational-Ring k)
      ( map-initial-hom-Ring ring-Rational-Ring (int-positive-ℤ k)) ＝
    one-Ring ring-Rational-Ring
  left-inverse-law-positive-integer-Rational-Ring (k , k>0) =
    is-left-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Ring)
      ( is-rational-ring-Rational-Ring k k>0)

  right-inverse-law-positive-integer-Rational-Ring :
    (k : ℤ⁺) →
    mul-Ring
      ( ring-Rational-Ring)
      ( map-initial-hom-Ring ring-Rational-Ring (int-positive-ℤ k))
      ( inv-positive-integer-Rational-Ring k) ＝
    one-Ring ring-Rational-Ring
  right-inverse-law-positive-integer-Rational-Ring (k , k>0) =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Ring)
      ( is-rational-ring-Rational-Ring k k>0)
```

## Properties

### ℚ is a rational ring

```agda
rational-ring-ℚ : Rational-Ring lzero
rational-ring-ℚ =
  ( ring-ℚ) ,
  ( inv-tr
    ( inverts-subset-hom-Ring
      ( ℤ-Ring)
      ( ring-ℚ)
      ( subtype-positive-ℤ))
      ( eq-initial-hom-ring-rational-ℤ)
      ( inverts-positive-integers-rational-ℤ))
```

### A ring `R` that admits a ring homomorphism `ℚ → R` is rational

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-has-rational-hom-Ring : hom-Ring ring-ℚ R → is-rational-Ring R
  is-rational-has-rational-hom-Ring f =
    inv-tr
      ( inverts-subset-hom-Ring
        ( ℤ-Ring)
        ( R)
        ( subtype-positive-ℤ))
      ( contraction-initial-hom-Ring
        ( R)
        ( comp-hom-Ring ℤ-Ring ring-ℚ R f hom-ring-rational-ℤ))
      ( inverts-positive-integers-rational-hom-Ring R f)
```

### The ring of rational numbers is the initial rational ring

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  map-initial-hom-Rational-Ring : ℚ → type-Rational-Ring R
  map-initial-hom-Rational-Ring x =
    mul-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-Ring (ring-Rational-Ring R) (numerator-ℚ x))
      ( inv-positive-integer-Rational-Ring R (positive-denominator-ℚ x))

{- TODO
  htpy-map-initial-hom-Rational-Ring :
    (f : hom-Ring ring-ℚ (ring-Rational-Ring R)) →
    map-initial-hom-Rational-Ring ~ map-hom-Ring ring-ℚ (ring-Rational-Ring R) f
  htpy-map-initial-hom-Rational-Ring f x = {!!}
 -}
```

TODO

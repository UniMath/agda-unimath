# The ring of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.ring-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.semigroups

open import ring-theory.homomorphisms-rings
open import ring-theory.localizations-rings
open import ring-theory.rings
```

</details>

## Idea

The
[additive group of rational numbers](elementary-number-theory.additive-group-of-rational-numbers.md)
equipped with
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a commutative [division ring](ring-theory.division-rings.md).

## Definitions

### The compatible multiplicative structure on the abelian group of rational numbers

```agda
has-mul-abelian-group-add-ℚ : has-mul-Ab abelian-group-add-ℚ
pr1 has-mul-abelian-group-add-ℚ = has-associative-mul-Semigroup semigroup-mul-ℚ
pr1 (pr2 has-mul-abelian-group-add-ℚ) = is-unital-mul-ℚ
pr1 (pr2 (pr2 has-mul-abelian-group-add-ℚ)) = left-distributive-mul-add-ℚ
pr2 (pr2 (pr2 has-mul-abelian-group-add-ℚ)) = right-distributive-mul-add-ℚ
```

### The ring of rational numbers

```agda
ring-ℚ : Ring lzero
pr1 ring-ℚ = abelian-group-add-ℚ
pr2 ring-ℚ = has-mul-abelian-group-add-ℚ
```

## Properties

### The ring of rational numbers is commutative

```agda
commutative-ring-ℚ : Commutative-Ring lzero
pr1 commutative-ring-ℚ = ring-ℚ
pr2 commutative-ring-ℚ = commutative-mul-ℚ
```

### The inclusion of integers in the rationals is the initial ring homomorphism

```agda
hom-ring-rational-ℤ : hom-Ring ℤ-Ring ring-ℚ
hom-ring-rational-ℤ =
  ( hom-add-rational-ℤ) ,
  ( λ {x y} → inv (mul-rational-ℤ x y)) ,
  ( refl)

abstract
  htpy-map-initial-hom-ring-rational-ℤ :
    map-initial-hom-Ring ring-ℚ ~ rational-ℤ
  htpy-map-initial-hom-ring-rational-ℤ =
    htpy-initial-hom-Ring ring-ℚ hom-ring-rational-ℤ

  eq-initial-hom-ring-rational-ℤ : initial-hom-Ring ring-ℚ ＝ hom-ring-rational-ℤ
  eq-initial-hom-ring-rational-ℤ =
    contraction-initial-hom-Ring ring-ℚ hom-ring-rational-ℤ
```

### The positive integers are invertible in ℚ

```agda
abstract
  inverts-positive-integers-rational-ℤ :
    inverts-subset-hom-Ring
      ( ℤ-Ring)
      ( ring-ℚ)
      ( subtype-positive-ℤ)
      ( hom-ring-rational-ℤ)
  inverts-positive-integers-rational-ℤ k k>0 =
    ( reciprocal-rational-ℤ⁺ (k , k>0)) ,
    ( right-inverse-law-reciprocal-rational-ℤ⁺ (k , k>0) ,
      left-inverse-law-reciprocal-rational-ℤ⁺ (k , k>0))
```

### Any ring homomorphism from ℚ inverts the positive integers

```agda
module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  abstract
    inverts-positive-integers-rational-hom-Ring :
      inverts-subset-hom-Ring
        ( ℤ-Ring)
        ( R)
        ( subtype-positive-ℤ)
        ( comp-hom-Ring ℤ-Ring ring-ℚ R f hom-ring-rational-ℤ)
    inverts-positive-integers-rational-hom-Ring k k>0 =
      preserves-invertible-elements-hom-Ring
        ( ring-ℚ)
        ( R)
        ( f)
        ( inverts-positive-integers-rational-ℤ k k>0)
```

## See also

- [`ring-extension-rational-numbers-of-rational-numbers`](elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers.md):
  the trivial
  [ring extension of `ℚ`](ring-theory.ring-extensions-rational-numbers.md) where
  it is proven that `ℚ` is the
  [localization](ring-theory.localizations-rings.md) of `ℤ` at `ℤ⁺`.

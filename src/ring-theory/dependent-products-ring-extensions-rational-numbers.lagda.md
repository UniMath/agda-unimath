# Dependent products of ring extensions of the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.dependent-products-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-integers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups

open import ring-theory.dependent-products-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.ring-extensions-rational-numbers
open import ring-theory.rings
```

</details>

## Idea

A [dependent product](ring-theory.dependent-products-rings.md) of
[ring extensions of ℚ](ring-theory.ring-extensions-rational-numbers.md) is a
ring extension of ℚ. This is the
{{#concept "product ring extension of ℚ" Agda=Π-Rational-Extension-Ring}} of a
family of ring extensions of ℚ.

## Definitions

### The product of ring extensions of `ℚ` is a ring extension of `ℚ`

```agda
module _
  {l1 l2 : Level} (I : UU l1) (R : I → Rational-Extension-Ring l2)
  where

  is-rational-extension-ring-Π-Rational-Extension-Ring :
    is-rational-extension-Ring (Π-Ring I (ring-Rational-Extension-Ring ∘ R))
  is-rational-extension-ring-Π-Rational-Extension-Ring k k>0 =
    ( λ i → inv-positive-integer-Rational-Extension-Ring (R i) (k , k>0)) ,
    ( eq-htpy
      ( λ i →
        inv-tr
          ( λ h →
            mul-Rational-Extension-Ring
              ( R i)
              ( map-hom-Ring
                ( ℤ-Ring)
                ( Π-Ring I (ring-Rational-Extension-Ring ∘ R))
                ( h)
                ( k)
                ( i))
              ( inv-positive-integer-Rational-Extension-Ring (R i) (k , k>0)) ＝
            one-Ring (ring-Rational-Extension-Ring (R i)))
          ( eq-initial-hom-Π-Ring I (ring-Rational-Extension-Ring ∘ R))
          ( right-inverse-law-positive-integer-Rational-Extension-Ring
            ( R i)
            ( k , k>0)))) ,
    ( eq-htpy
      ( λ i →
        inv-tr
          ( λ h →
            mul-Rational-Extension-Ring
              ( R i)
              ( inv-positive-integer-Rational-Extension-Ring (R i) (k , k>0))
              ( map-hom-Ring
                ( ℤ-Ring)
                ( Π-Ring I (ring-Rational-Extension-Ring ∘ R))
                ( h)
                ( k)
                ( i)) ＝
            one-Ring (ring-Rational-Extension-Ring (R i)))
          ( eq-initial-hom-Π-Ring I (ring-Rational-Extension-Ring ∘ R))
          ( left-inverse-law-positive-integer-Rational-Extension-Ring
            ( R i)
            ( k , k>0))))

  Π-Rational-Extension-Ring : Rational-Extension-Ring (l1 ⊔ l2)
  Π-Rational-Extension-Ring =
    ( Π-Ring I (ring-Rational-Extension-Ring ∘ R)) ,
    ( is-rational-extension-ring-Π-Rational-Extension-Ring)
```

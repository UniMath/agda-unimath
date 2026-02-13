# Bilinear maps on vector spaces

```agda
module linear-algebra.bilinear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.bilinear-maps-left-modules-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

A
{{#concept "bilinear map" Disambiguation="from two left modules over commutative rings to a third" Agda=bilinear-map-left-module-Commutative-Ring}}
from two [left modules](linear-algebra.left-modules-commutative-rings.md) `X`
and `Y` over a [commutative ring](commutative-algebra.commutative-rings.md) `R`
to a third module `Z` is a map `f : X → Y → Z` which is
[linear](linear-algebra.linear-maps-left-modules-commutative-rings.md) in each
argument.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Ring l1)
  (X : left-module-Commutative-Ring l2 R)
  (Y : left-module-Commutative-Ring l3 R)
  (Z : left-module-Commutative-Ring l4 R)
  (f :
    type-left-module-Commutative-Ring R X →
    type-left-module-Commutative-Ring R Y →
    type-left-module-Commutative-Ring R Z)
  where

  is-linear-on-left-prop-binary-map-left-module-Commutative-Ring :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-left-prop-binary-map-left-module-Commutative-Ring =
    is-linear-on-left-prop-binary-map-left-module-Ring
      ( ring-Commutative-Ring R)
      ( X)
      ( Y)
      ( Z)
      ( f)

  is-linear-on-left-binary-map-left-module-Commutative-Ring :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-left-binary-map-left-module-Commutative-Ring =
    type-Prop is-linear-on-left-prop-binary-map-left-module-Commutative-Ring

  is-linear-on-right-prop-binary-map-left-module-Commutative-Ring :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-right-prop-binary-map-left-module-Commutative-Ring =
    is-linear-on-right-prop-binary-map-left-module-Ring
      ( ring-Commutative-Ring R)
      ( X)
      ( Y)
      ( Z)
      ( f)

  is-linear-on-right-binary-map-left-module-Commutative-Ring :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-right-binary-map-left-module-Commutative-Ring =
    type-Prop is-linear-on-right-prop-binary-map-left-module-Commutative-Ring

  is-bilinear-map-prop-left-module-Commutative-Ring : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-bilinear-map-prop-left-module-Commutative-Ring =
    is-bilinear-map-prop-left-module-Ring
      ( ring-Commutative-Ring R)
      ( X)
      ( Y)
      ( Z)
      ( f)

  is-bilinear-map-left-module-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-bilinear-map-left-module-Commutative-Ring =
    type-Prop is-bilinear-map-prop-left-module-Commutative-Ring

bilinear-map-left-module-Commutative-Ring :
  {l1 l2 l3 l4 : Level} (R : Commutative-Ring l1) →
  left-module-Commutative-Ring l2 R →
  left-module-Commutative-Ring l3 R →
  left-module-Commutative-Ring l4 R →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
bilinear-map-left-module-Commutative-Ring R X Y Z =
  type-subtype (is-bilinear-map-prop-left-module-Commutative-Ring R X Y Z)
```

## Properties

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Ring l1)
  (X : left-module-Commutative-Ring l2 R)
  (Y : left-module-Commutative-Ring l3 R)
  (Z : left-module-Commutative-Ring l4 R)
  (f : bilinear-map-left-module-Commutative-Ring R X Y Z)
  where

  map-bilinear-map-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring R X →
    type-left-module-Commutative-Ring R Y →
    type-left-module-Commutative-Ring R Z
  map-bilinear-map-left-module-Commutative-Ring = pr1 f
```

### Linear maps from bilinear maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Ring l1)
  (X : left-module-Commutative-Ring l2 R)
  (Y : left-module-Commutative-Ring l3 R)
  (Z : left-module-Commutative-Ring l4 R)
  (f : bilinear-map-left-module-Commutative-Ring R X Y Z)
  where

  linear-map-ev-right-bilinear-map-left-module-Commutative-Ring :
    (y : type-left-module-Commutative-Ring R Y) →
    linear-map-left-module-Commutative-Ring R X Z
  linear-map-ev-right-bilinear-map-left-module-Commutative-Ring =
    linear-map-ev-right-bilinear-map-left-module-Ring
      ( ring-Commutative-Ring R)
      ( X)
      ( Y)
      ( Z)
      ( f)

  linear-map-ev-left-bilinear-map-left-module-Commutative-Ring :
    (x : type-left-module-Commutative-Ring R X) →
    linear-map-left-module-Commutative-Ring R Y Z
  linear-map-ev-left-bilinear-map-left-module-Commutative-Ring =
    linear-map-ev-left-bilinear-map-left-module-Ring
      ( ring-Commutative-Ring R)
      ( X)
      ( Y)
      ( Z)
      ( f)
```

### Zero laws of bilinear maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Commutative-Ring l1)
  (X : left-module-Commutative-Ring l2 R)
  (Y : left-module-Commutative-Ring l3 R)
  (Z : left-module-Commutative-Ring l4 R)
  (f : bilinear-map-left-module-Commutative-Ring R X Y Z)
  where

  abstract
    left-zero-law-bilinear-map-left-module-Commutative-Ring :
      (y : type-left-module-Commutative-Ring R Y) →
      map-bilinear-map-left-module-Commutative-Ring R X Y Z f
        ( zero-left-module-Commutative-Ring R X)
        ( y) ＝
      zero-left-module-Commutative-Ring R Z
    left-zero-law-bilinear-map-left-module-Commutative-Ring =
      left-zero-law-bilinear-map-left-module-Ring
        ( ring-Commutative-Ring R)
        ( X)
        ( Y)
        ( Z)
        ( f)

    right-zero-law-bilinear-map-left-module-Commutative-Ring :
      (x : type-left-module-Commutative-Ring R X) →
      map-bilinear-map-left-module-Commutative-Ring R X Y Z f
        ( x)
        ( zero-left-module-Commutative-Ring R Y) ＝
      zero-left-module-Commutative-Ring R Z
    right-zero-law-bilinear-map-left-module-Commutative-Ring =
      right-zero-law-bilinear-map-left-module-Ring
        ( ring-Commutative-Ring R)
        ( X)
        ( Y)
        ( Z)
        ( f)
```

## See also

- [Bilinear maps on left modules over rings](linear-algebra.bilinear-maps-left-modules-rings.md)

## External links

- [Bilinear map](https://en.wikipedia.org/wiki/Bilinear_map#Modules) on
  Wikipedia

# Bilinear maps on left modules over rings

```agda
module linear-algebra.bilinear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "bilinear map" Disambiguation="from two left modules over a ring to a third" Agda=bilinear-map-left-module-Ring}}
from two [left modules](linear-algebra.left-modules-rings.md) `X` and `Y` over a
[ring](ring-theory.rings.md) `R` to a third module `Z` is a map `f : X → Y → Z`
which is [linear](linear-algebra.linear-maps-left-modules-rings.md) in each
argument.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Ring l1)
  (X : left-module-Ring l2 R)
  (Y : left-module-Ring l3 R)
  (Z : left-module-Ring l4 R)
  (f :
    type-left-module-Ring R X → type-left-module-Ring R Y →
    type-left-module-Ring R Z)
  where

  is-linear-on-left-prop-binary-map-left-module-Ring : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-left-prop-binary-map-left-module-Ring =
    Π-Prop
      ( type-left-module-Ring R Y)
      ( λ y → is-linear-map-prop-left-module-Ring R X Z (λ x → f x y))

  is-linear-on-left-binary-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-left-binary-map-left-module-Ring =
    type-Prop is-linear-on-left-prop-binary-map-left-module-Ring

  is-linear-on-right-prop-binary-map-left-module-Ring : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-right-prop-binary-map-left-module-Ring =
    Π-Prop
      ( type-left-module-Ring R X)
      ( λ x → is-linear-map-prop-left-module-Ring R Y Z (f x))

  is-linear-on-right-binary-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-right-binary-map-left-module-Ring =
    type-Prop is-linear-on-right-prop-binary-map-left-module-Ring

  is-bilinear-map-prop-left-module-Ring : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-bilinear-map-prop-left-module-Ring =
    is-linear-on-left-prop-binary-map-left-module-Ring ∧
    is-linear-on-right-prop-binary-map-left-module-Ring

  is-bilinear-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-bilinear-map-left-module-Ring =
    type-Prop is-bilinear-map-prop-left-module-Ring

bilinear-map-left-module-Ring :
  {l1 l2 l3 l4 : Level} (R : Ring l1) →
  left-module-Ring l2 R → left-module-Ring l3 R → left-module-Ring l4 R →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
bilinear-map-left-module-Ring R X Y Z =
  type-subtype (is-bilinear-map-prop-left-module-Ring R X Y Z)
```

## Properties

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Ring l1)
  (X : left-module-Ring l2 R)
  (Y : left-module-Ring l3 R)
  (Z : left-module-Ring l4 R)
  (f : bilinear-map-left-module-Ring R X Y Z)
  where

  map-bilinear-map-left-module-Ring :
    type-left-module-Ring R X →
    type-left-module-Ring R Y →
    type-left-module-Ring R Z
  map-bilinear-map-left-module-Ring = pr1 f
```

### Linear maps from bilinear maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Ring l1)
  (X : left-module-Ring l2 R)
  (Y : left-module-Ring l3 R)
  (Z : left-module-Ring l4 R)
  (f : bilinear-map-left-module-Ring R X Y Z)
  where

  linear-map-ev-right-bilinear-map-left-module-Ring :
    (y : type-left-module-Ring R Y) →
    linear-map-left-module-Ring R X Z
  linear-map-ev-right-bilinear-map-left-module-Ring y =
    ( ( λ x → map-bilinear-map-left-module-Ring R X Y Z f x y) ,
      pr1 (pr2 f) y)

  linear-map-ev-left-bilinear-map-left-module-Ring :
    (x : type-left-module-Ring R X) →
    linear-map-left-module-Ring R Y Z
  linear-map-ev-left-bilinear-map-left-module-Ring x =
    ( map-bilinear-map-left-module-Ring R X Y Z f x ,
      pr2 (pr2 f) x)
```

### Zero laws of bilinear maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Ring l1)
  (X : left-module-Ring l2 R)
  (Y : left-module-Ring l3 R)
  (Z : left-module-Ring l4 R)
  (f : bilinear-map-left-module-Ring R X Y Z)
  where

  abstract
    left-zero-law-bilinear-map-left-module-Ring :
      (y : type-left-module-Ring R Y) →
      map-bilinear-map-left-module-Ring R X Y Z f
        ( zero-left-module-Ring R X)
        ( y) ＝
      zero-left-module-Ring R Z
    left-zero-law-bilinear-map-left-module-Ring y =
      is-zero-map-zero-linear-map-left-module-Ring R X Z
        ( linear-map-ev-right-bilinear-map-left-module-Ring R X Y Z f y)

    right-zero-law-bilinear-map-left-module-Ring :
      (x : type-left-module-Ring R X) →
      map-bilinear-map-left-module-Ring R X Y Z f
        ( x)
        ( zero-left-module-Ring R Y) ＝
      zero-left-module-Ring R Z
    right-zero-law-bilinear-map-left-module-Ring x =
      is-zero-map-zero-linear-map-left-module-Ring R Y Z
        ( linear-map-ev-left-bilinear-map-left-module-Ring R X Y Z f x)
```

## See also

- [Bilinear maps on left modules over commutative rings](linear-algebra.bilinear-maps-left-modules-commutative-rings.md)

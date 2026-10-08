# Scalar multiplication of linear maps between left modules over commutative rings

```agda
module linear-algebra.scalar-multiplication-linear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.addition-linear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-endomaps-left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

Given a
[linear map](linear-algebra.linear-maps-left-modules-commutative-rings.md) `f`
from a [left module](linear-algebra.left-modules-commutative-rings.md) `M` over
a [commutative ring](commutative-algebra.commutative-rings.md) `R` to another
left module `N` over `R`, and a constant `c : R`, the map `x ↦ c * f x` is a
linear map.

## Definition

### The linear endomap of scalar multiplication

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (r : type-Commutative-Ring R)
  where

  is-linear-map-mul-left-module-Commutative-Ring :
    is-linear-endo-left-module-Commutative-Ring R M
      ( mul-left-module-Commutative-Ring R M r)
  is-linear-map-mul-left-module-Commutative-Ring =
    ( left-distributive-mul-add-left-module-Commutative-Ring R M r ,
      left-swap-mul-left-module-Commutative-Ring R M r)

  linear-endo-mul-left-module-Commutative-Ring :
    linear-endo-left-module-Commutative-Ring R M
  linear-endo-mul-left-module-Commutative-Ring =
    ( mul-left-module-Commutative-Ring R M r ,
      is-linear-map-mul-left-module-Commutative-Ring)
```

### Scalar multiplication of linear maps

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  (r : type-Commutative-Ring R)
  where

  mul-linear-map-left-module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring R M N →
    linear-map-left-module-Commutative-Ring R M N
  mul-linear-map-left-module-Commutative-Ring =
    comp-linear-map-left-module-Commutative-Ring R M N N
      ( linear-endo-mul-left-module-Commutative-Ring R N r)
```

## Properties

### Scalar multiplication of linear maps distributes over addition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  abstract
    left-distributive-mul-add-linear-map-left-module-Commutative-Ring :
      (r : type-Commutative-Ring R)
      (f g : linear-map-left-module-Commutative-Ring R M N) →
      mul-linear-map-left-module-Commutative-Ring R M N
        ( r)
        ( add-linear-map-left-module-Commutative-Ring R M N f g) ＝
      add-linear-map-left-module-Commutative-Ring R M N
        ( mul-linear-map-left-module-Commutative-Ring R M N r f)
        ( mul-linear-map-left-module-Commutative-Ring R M N r g)
    left-distributive-mul-add-linear-map-left-module-Commutative-Ring r f g =
      eq-htpy-linear-map-left-module-Commutative-Ring R M N _ _
        ( λ x →
          left-distributive-mul-add-left-module-Commutative-Ring R N r _ _)

    right-distributive-mul-add-linear-map-left-module-Commutative-Ring :
      (r s : type-Commutative-Ring R)
      (f : linear-map-left-module-Commutative-Ring R M N) →
      mul-linear-map-left-module-Commutative-Ring R M N
        ( add-Commutative-Ring R r s)
        ( f) ＝
      add-linear-map-left-module-Commutative-Ring R M N
        ( mul-linear-map-left-module-Commutative-Ring R M N r f)
        ( mul-linear-map-left-module-Commutative-Ring R M N s f)
    right-distributive-mul-add-linear-map-left-module-Commutative-Ring r s f =
      eq-htpy-linear-map-left-module-Commutative-Ring R M N _ _
        ( λ x →
          right-distributive-mul-add-left-module-Commutative-Ring R N r s _)
```

### Multiplication by one is the identity

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  abstract
    left-unit-law-mul-linear-map-left-module-Commutative-Ring :
      (f : linear-map-left-module-Commutative-Ring R M N) →
      mul-linear-map-left-module-Commutative-Ring R M N
        ( one-Commutative-Ring R)
        ( f) ＝
      f
    left-unit-law-mul-linear-map-left-module-Commutative-Ring f =
      eq-htpy-linear-map-left-module-Commutative-Ring R M N _ _
        ( λ x →
          left-unit-law-mul-left-module-Commutative-Ring R N _)
```

### Multiplication is associative

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  abstract
    associative-mul-linear-map-left-module-Commutative-Ring :
      (r s : type-Commutative-Ring R)
      (f : linear-map-left-module-Commutative-Ring R M N) →
      mul-linear-map-left-module-Commutative-Ring R M N
        ( mul-Commutative-Ring R r s)
        ( f) ＝
      mul-linear-map-left-module-Commutative-Ring R M N
        ( r)
        ( mul-linear-map-left-module-Commutative-Ring R M N s f)
    associative-mul-linear-map-left-module-Commutative-Ring r s f =
      eq-htpy-linear-map-left-module-Commutative-Ring R M N _ _
        ( λ x → associative-mul-left-module-Commutative-Ring R N r s _)
```

# Scalar multiplication of linear maps between left modules over commutative rings

```agda
module linear-algebra.scalar-multiplication-linear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
open import linear-algebra.linear-transformations-left-modules-commutative-rings
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

### The linear transformation of scalar multiplication

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (r : type-Commutative-Ring R)
  where

  is-linear-mul-left-module-Commutative-Ring :
    is-linear-transform-left-module-Commutative-Ring R M
      ( mul-left-module-Commutative-Ring R M r)
  is-linear-mul-left-module-Commutative-Ring =
    ( left-distributive-mul-add-left-module-Commutative-Ring R M r ,
      left-swap-mul-left-module-Commutative-Ring R M r)

  linear-transform-mul-left-module-Commutative-Ring :
    linear-transform-left-module-Commutative-Ring R M
  linear-transform-mul-left-module-Commutative-Ring =
    ( mul-left-module-Commutative-Ring R M r ,
      is-linear-mul-left-module-Commutative-Ring)
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
      ( linear-transform-mul-left-module-Commutative-Ring R N r)
```

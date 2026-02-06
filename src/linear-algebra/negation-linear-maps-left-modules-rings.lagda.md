# Negation of linear maps between left modules over rings

```agda
module linear-algebra.negation-linear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

Given a [linear map](linear-algebra.linear-maps-left-modules-rings.md) `f` from
a [left module](linear-algebra.left-modules-rings.md) `M` over a
[ring](ring-theory.rings.md) `R` to another left module `N` over `R`, the map
`x ↦ -(f x)` is a linear map.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f : linear-map-left-module-Ring R M N)
  where

  neg-map-linear-map-left-module-Ring :
    type-left-module-Ring R M → type-left-module-Ring R N
  neg-map-linear-map-left-module-Ring x =
    neg-left-module-Ring R N (map-linear-map-left-module-Ring R M N f x)

  abstract
    is-additive-neg-map-linear-map-left-module-Ring :
      is-additive-map-left-module-Ring R M N neg-map-linear-map-left-module-Ring
    is-additive-neg-map-linear-map-left-module-Ring x y =
      ( ap
        ( neg-left-module-Ring R N)
        ( is-additive-map-linear-map-left-module-Ring R M N f x y)) ∙
      ( distributive-neg-add-left-module-Ring R N _ _)

    is-homogeneous-neg-map-linear-map-left-module-Ring :
      is-homogeneous-map-left-module-Ring R M N
        ( neg-map-linear-map-left-module-Ring)
    is-homogeneous-neg-map-linear-map-left-module-Ring c x =
      ( ap
        ( neg-left-module-Ring R N)
        ( is-homogeneous-map-linear-map-left-module-Ring R M N f c x)) ∙
      ( inv (right-negative-law-mul-left-module-Ring R N c _))

  is-linear-neg-map-linear-map-left-module-Ring :
    is-linear-map-left-module-Ring R M N neg-map-linear-map-left-module-Ring
  is-linear-neg-map-linear-map-left-module-Ring =
    ( is-additive-neg-map-linear-map-left-module-Ring ,
      is-homogeneous-neg-map-linear-map-left-module-Ring)

  neg-linear-map-left-module-Ring : linear-map-left-module-Ring R M N
  neg-linear-map-left-module-Ring =
    ( neg-map-linear-map-left-module-Ring ,
      is-linear-neg-map-linear-map-left-module-Ring)
```

## Properties

### Negation of a linear map is an involution

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f : linear-map-left-module-Ring R M N)
  where

  abstract
    neg-neg-linear-map-left-module-Ring :
      neg-linear-map-left-module-Ring R M N
        ( neg-linear-map-left-module-Ring R M N f) ＝
      f
    neg-neg-linear-map-left-module-Ring =
      eq-htpy-linear-map-left-module-Ring R M N _ _
        ( λ x → neg-neg-left-module-Ring R N _)
```

# Duals of left modules over commutative rings

```agda
module linear-algebra.duals-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.left-module-linear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-forms-left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

The
{{#concept "dual" Disambiguation="of a left module over a commutative ring" Agda=dual-left-module-Commutative-Ring}}
of a [left module](linear-algebra.left-modules-commutative-rings.md) `M` over a
[commutative ring](commutative-algebra.commutative-rings.md) is the left module
of [linear forms](linear-algebra.linear-forms-left-modules-commutative-rings.md)
in `M`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  dual-left-module-Commutative-Ring : left-module-Commutative-Ring (l1 ⊔ l2) R
  dual-left-module-Commutative-Ring =
    left-module-linear-map-left-module-Commutative-Ring
      ( R)
      ( M)
      ( left-module-commutative-ring-Commutative-Ring R)
```

## Properties

### The canonical linear map from a left module to its double dual

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  map-double-dual-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring R M →
    linear-form-left-module-Commutative-Ring
      ( R)
      ( dual-left-module-Commutative-Ring R M)
  map-double-dual-left-module-Commutative-Ring =
    linear-map-ev-linear-map-left-module-Commutative-Ring
      ( R)
      ( M)
      ( left-module-commutative-ring-Commutative-Ring R)

  abstract
    is-additive-map-double-dual-left-module-Commutative-Ring :
      is-additive-map-left-module-Commutative-Ring
        ( R)
        ( M)
        ( dual-left-module-Commutative-Ring R
          ( dual-left-module-Commutative-Ring R M))
        ( map-double-dual-left-module-Commutative-Ring)
    is-additive-map-double-dual-left-module-Commutative-Ring x y =
      eq-htpy-linear-map-left-module-Commutative-Ring
        ( R)
        ( dual-left-module-Commutative-Ring R M)
        ( left-module-commutative-ring-Commutative-Ring R)
        ( _)
        ( _)
        ( λ f →
          is-additive-map-linear-map-left-module-Commutative-Ring R
            ( M)
            ( left-module-commutative-ring-Commutative-Ring R)
            ( f)
            ( x)
            ( y))

    is-homogeneous-map-double-dual-left-module-Commutative-Ring :
      is-homogeneous-map-left-module-Commutative-Ring
        ( R)
        ( M)
        ( dual-left-module-Commutative-Ring R
          ( dual-left-module-Commutative-Ring R M))
        ( map-double-dual-left-module-Commutative-Ring)
    is-homogeneous-map-double-dual-left-module-Commutative-Ring r x =
      eq-htpy-linear-map-left-module-Commutative-Ring
        ( R)
        ( dual-left-module-Commutative-Ring R M)
        ( left-module-commutative-ring-Commutative-Ring R)
        ( _)
        ( _)
        ( λ f →
          is-homogeneous-map-linear-map-left-module-Commutative-Ring R
            ( M)
            ( left-module-commutative-ring-Commutative-Ring R)
            ( f)
            ( r)
            ( x))

  linear-map-double-dual-left-module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring
      ( R)
      ( M)
      ( dual-left-module-Commutative-Ring R
        ( dual-left-module-Commutative-Ring R M))
  linear-map-double-dual-left-module-Commutative-Ring =
    ( map-double-dual-left-module-Commutative-Ring ,
      is-additive-map-double-dual-left-module-Commutative-Ring ,
      is-homogeneous-map-double-dual-left-module-Commutative-Ring)
```

# Eigenmodules of linear transformations of left modules over commutative rings

```agda
module spectral-theory.eigenmodules-linear-endomaps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.left-submodules-commutative-rings
open import linear-algebra.linear-endomaps-left-modules-commutative-rings
open import linear-algebra.subsets-left-modules-commutative-rings

open import spectral-theory.eigenvalues-eigenelements-linear-endomaps-left-modules-commutative-rings
```

</details>

## Idea

Given a
[linear endomap](linear-algebra.linear-endomaps-left-modules-commutative-rings.md)
`f` of a [left module](linear-algebra.left-modules-commutative-rings.md) `M`
over a [commutative ring](commutative-algebra.commutative-rings.md) `R`, the
{{#concept "eigenmodule" Disambiguation="of a linear endomap of a left module over a commutative ring" Agda=eigenmodule-linear-endo-left-module-Commutative-Ring}}
of `r : R` is the
[subset](linear-algebra.subsets-left-modules-commutative-rings.md) of elements
of `M` with the
[eigenvalue](spectral-theory.eigenvalues-eigenelements-linear-endomaps-left-modules-commutative-rings.md)
`r`. This subset is a
[submodule](linear-algebra.left-submodules-commutative-rings.md) of `M`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  (r : type-Commutative-Ring R)
  where

  subset-eigenmodule-linear-endo-left-module-Commutative-Ring :
    subset-left-module-Commutative-Ring l2 R M
  subset-eigenmodule-linear-endo-left-module-Commutative-Ring =
    is-eigenelement-eigenvalue-prop-linear-endo-left-module-Commutative-Ring
      ( R)
      ( M)
      ( f)
      ( r)
```

## Properties

### The subset associated with an eigenmodule is closed under addition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  (r : type-Commutative-Ring R)
  where

  abstract
    is-closed-under-addition-subset-eigenmodule-linear-endo-left-module-Commutative-Ring :
      is-closed-under-addition-subset-left-module-Commutative-Ring R M
        ( subset-eigenmodule-linear-endo-left-module-Commutative-Ring
          ( R)
          ( M)
          ( f)
          ( r))
    is-closed-under-addition-subset-eigenmodule-linear-endo-left-module-Commutative-Ring
      x y fx=rx fy=ry =
      equational-reasoning
      map-linear-endo-left-module-Commutative-Ring R M f
        ( add-left-module-Commutative-Ring R M x y)
      ＝
        add-left-module-Commutative-Ring R M
          ( map-linear-endo-left-module-Commutative-Ring R M f x)
          ( map-linear-endo-left-module-Commutative-Ring R M f y)
        by
          is-additive-map-linear-endo-left-module-Commutative-Ring
            ( R)
            ( M)
            ( f)
            ( x)
            ( y)
      ＝
        add-left-module-Commutative-Ring R M
          ( mul-left-module-Commutative-Ring R M r x)
          ( mul-left-module-Commutative-Ring R M r y)
        by ap-binary (add-left-module-Commutative-Ring R M) fx=rx fy=ry
      ＝
        mul-left-module-Commutative-Ring R M
          ( r)
          ( add-left-module-Commutative-Ring R M x y)
        by
          inv (left-distributive-mul-add-left-module-Commutative-Ring R M r x y)
```

### The subset associated with an eigenmodule is closed under scalar multiplication

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  (r : type-Commutative-Ring R)
  where

  abstract
    is-closed-under-scalar-multiplication-subset-eigenmodule-linear-endo-left-module-Commutative-Ring :
      is-closed-under-scalar-multiplication-subset-left-module-Commutative-Ring
        ( R)
        ( M)
        ( subset-eigenmodule-linear-endo-left-module-Commutative-Ring
          ( R)
          ( M)
          ( f)
          ( r))
    is-closed-under-scalar-multiplication-subset-eigenmodule-linear-endo-left-module-Commutative-Ring
      s x fx=rx =
      equational-reasoning
      map-linear-endo-left-module-Commutative-Ring R M f
        ( mul-left-module-Commutative-Ring R M s x)
      ＝
        mul-left-module-Commutative-Ring R M
          ( s)
          ( map-linear-endo-left-module-Commutative-Ring R M f x)
        by
          is-homogeneous-map-linear-endo-left-module-Commutative-Ring
            ( R)
            ( M)
            ( f)
            ( s)
            ( _)
      ＝
        mul-left-module-Commutative-Ring R M
          ( s)
          ( mul-left-module-Commutative-Ring R M r x)
        by ap (mul-left-module-Commutative-Ring R M s) fx=rx
      ＝
        mul-left-module-Commutative-Ring R M
          ( r)
          ( mul-left-module-Commutative-Ring R M s x)
        by left-swap-mul-left-module-Commutative-Ring R M s r x
```

### The subset of elements `x` with `f x = r * x` is a submodule

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  (r : type-Commutative-Ring R)
  where

  eigenmodule-linear-endo-left-module-Commutative-Ring :
    left-submodule-Commutative-Ring l2 R M
  eigenmodule-linear-endo-left-module-Commutative-Ring =
    ( subset-eigenmodule-linear-endo-left-module-Commutative-Ring R M f r ,
      is-eigenelement-zero-linear-endo-left-module-Commutative-Ring
        ( R)
        ( M)
        ( f)
        ( r) ,
      is-closed-under-addition-subset-eigenmodule-linear-endo-left-module-Commutative-Ring
        ( R)
        ( M)
        ( f)
        ( r) ,
      is-closed-under-scalar-multiplication-subset-eigenmodule-linear-endo-left-module-Commutative-Ring
        ( R)
        ( M)
        ( f)
        ( r))

  left-eigenmodule-linear-endo-left-module-Commutative-Ring :
    left-module-Commutative-Ring l2 R
  left-eigenmodule-linear-endo-left-module-Commutative-Ring =
    left-module-left-submodule-Commutative-Ring
      ( R)
      ( M)
      ( eigenmodule-linear-endo-left-module-Commutative-Ring)
```

## See also

- [Eigenspaces of linear transformations of vector spaces](spectral-theory.eigenspaces-linear-endomaps-vector-spaces.md)

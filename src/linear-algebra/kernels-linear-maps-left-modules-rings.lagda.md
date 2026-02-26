# Kernels of linear maps between left modules over rings

```agda
module linear-algebra.kernels-linear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.kernels-homomorphisms-abelian-groups
open import group-theory.subgroups-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.left-submodules-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.subsets-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "kernel" WDID=Q2914509 WD="kernel" Disambiguation="of a linear map between left modules over rings" Agda=kernel-linear-map-left-module-Ring}}
of a [linear map](linear-algebra.linear-maps-left-modules-rings.md) from a
[left module](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) to another left module over the same ring is the
preimage of zero under the linear map.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f : linear-map-left-module-Ring R M N)
  where

  kernel-hom-ab-linear-map-left-module-Ring :
    Subgroup-Ab l3 (ab-left-module-Ring R M)
  kernel-hom-ab-linear-map-left-module-Ring =
    kernel-hom-Ab
      ( ab-left-module-Ring R M)
      ( ab-left-module-Ring R N)
      ( hom-ab-linear-map-left-module-Ring R M N f)

  subset-kernel-linear-map-left-module-Ring :
    subset-left-module-Ring l3 R M
  subset-kernel-linear-map-left-module-Ring =
    subset-Subgroup-Ab
      ( ab-left-module-Ring R M)
      ( kernel-hom-ab-linear-map-left-module-Ring)
```

## Properties

### The kernel of a linear map is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f : linear-map-left-module-Ring R M N)
  where

  abstract
    is-closed-under-addition-subset-kernel-linear-map-left-module-Ring :
      is-closed-under-addition-subset-left-module-Ring
        ( R)
        ( M)
        ( subset-kernel-linear-map-left-module-Ring R M N f)
    is-closed-under-addition-subset-kernel-linear-map-left-module-Ring _ _ =
      is-closed-under-addition-subset-kernel-hom-Ab
      ( ab-left-module-Ring R M)
      ( ab-left-module-Ring R N)
      ( hom-ab-linear-map-left-module-Ring R M N f)
```

### The kernel of a linear map is closed under scalar multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f : linear-map-left-module-Ring R M N)
  where

  abstract
    is-closed-under-multiplication-subset-kernel-linear-map-left-module-Ring :
      is-closed-under-scalar-multiplication-subset-left-module-Ring
        ( R)
        ( M)
        ( subset-kernel-linear-map-left-module-Ring R M N f)
    is-closed-under-multiplication-subset-kernel-linear-map-left-module-Ring
      c x 0=fx =
      inv
        ( equational-reasoning
          map-linear-map-left-module-Ring R M N f
            ( mul-left-module-Ring R M c x)
          ＝
            mul-left-module-Ring R N c
              ( map-linear-map-left-module-Ring R M N f x)
            by is-homogeneous-map-linear-map-left-module-Ring R M N f c x
          ＝ mul-left-module-Ring R N c (zero-left-module-Ring R N)
            by ap (mul-left-module-Ring R N c) (inv 0=fx)
          ＝ zero-left-module-Ring R N
            by right-zero-law-mul-left-module-Ring R N c)
```

### The kernel of a linear map is a submodule

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f : linear-map-left-module-Ring R M N)
  where

  is-left-submodule-kernel-linear-map-left-module-Ring :
    is-left-submodule-Ring R M
      ( subset-kernel-linear-map-left-module-Ring R M N f)
  is-left-submodule-kernel-linear-map-left-module-Ring =
    ( inv (is-zero-map-zero-linear-map-left-module-Ring R M N f) ,
      is-closed-under-addition-subset-kernel-linear-map-left-module-Ring
        ( R)
        ( M)
        ( N)
        ( f) ,
      is-closed-under-multiplication-subset-kernel-linear-map-left-module-Ring
        ( R)
        ( M)
        ( N)
        ( f))

  kernel-linear-map-left-module-Ring : left-submodule-Ring l3 R M
  kernel-linear-map-left-module-Ring =
    ( subset-kernel-linear-map-left-module-Ring R M N f ,
      is-left-submodule-kernel-linear-map-left-module-Ring)

  left-module-kernel-linear-map-left-module-Ring : left-module-Ring (l2 ⊔ l3) R
  left-module-kernel-linear-map-left-module-Ring =
    left-module-left-submodule-Ring R M kernel-linear-map-left-module-Ring
```

## See also

- [Kernels of linear maps of vector spaces](linear-algebra.kernels-linear-maps-vector-spaces.md)

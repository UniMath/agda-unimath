# Kernels of linear maps between left modules over commutative rings

```agda
module linear-algebra.kernels-linear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.kernels-linear-maps-left-modules-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.left-submodules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
open import linear-algebra.subsets-left-modules-commutative-rings
```

</details>

## Idea

The
{{#concept "kernel" WDID=Q2914509 WD="kernel" Disambiguation="of a linear map between left modules over commutative rings" Agda=kernel-linear-map-left-module-Commutative-Ring}},
or **null space**, of a
[linear map](linear-algebra.linear-maps-left-modules-commutative-rings.md) from
a [left module](linear-algebra.left-modules-commutative-rings.md) over a
[commutative ring](commutative-algebra.commutative-rings.md) to another left
module over the same ring is the preimage of zero under the linear map.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  (f : linear-map-left-module-Commutative-Ring R M N)
  where

  subset-kernel-linear-map-left-module-Commutative-Ring :
    subset-left-module-Commutative-Ring l3 R M
  subset-kernel-linear-map-left-module-Commutative-Ring =
    subset-kernel-linear-map-left-module-Ring (ring-Commutative-Ring R) M N f

  kernel-linear-map-left-module-Commutative-Ring :
    left-submodule-Commutative-Ring l3 R M
  kernel-linear-map-left-module-Commutative-Ring =
    kernel-linear-map-left-module-Ring
      ( ring-Commutative-Ring R)
      ( M)
      ( N)
      ( f)

  left-module-kernel-linear-map-left-module-Commutative-Ring :
    left-module-Commutative-Ring (l2 ⊔ l3) R
  left-module-kernel-linear-map-left-module-Commutative-Ring =
    left-module-kernel-linear-map-left-module-Ring
      ( ring-Commutative-Ring R)
      ( M)
      ( N)
      ( f)
```

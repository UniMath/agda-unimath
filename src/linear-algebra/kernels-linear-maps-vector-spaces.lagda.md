# Kernels of linear maps between vector spaces

```agda
module linear-algebra.kernels-linear-maps-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.kernels-linear-maps-left-modules-rings
open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.subspaces-vector-spaces
open import linear-algebra.vector-spaces
```

</details>

## Idea

The
{{#concept "kernel" Disambiguation="of a linear map of vector spaces" WDID=Q2914509 WD="kernel" Agda=kernel-linear-map-Vector-Space}}
of a [linear map](linear-algebra.linear-maps-vector-spaces.md) between
[vector spaces](linear-algebra.vector-spaces.md) is the preimage of zero.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  (f : linear-map-Vector-Space F V W)
  where

  subset-kernel-linear-map-Vector-Space : subtype l3 (type-Vector-Space F V)
  subset-kernel-linear-map-Vector-Space =
    subset-kernel-linear-map-left-module-Ring (ring-Heyting-Field F) V W f

  kernel-linear-map-Vector-Space : subspace-Vector-Space l3 F V
  kernel-linear-map-Vector-Space =
    kernel-linear-map-left-module-Ring (ring-Heyting-Field F) V W f

  subspace-kernel-linear-map-Vector-Space : Vector-Space (l2 ⊔ l3) F
  subspace-kernel-linear-map-Vector-Space =
    left-module-kernel-linear-map-left-module-Ring (ring-Heyting-Field F) V W f
```

## See also

- [Kernels of linear maps of left modules](linear-algebra.kernels-linear-maps-left-modules-rings.md)

## External links

- [Kernel (linear algebra)](<https://en.wikipedia.org/wiki/Kernel_(linear_algebra)>)
  on Wikipedia

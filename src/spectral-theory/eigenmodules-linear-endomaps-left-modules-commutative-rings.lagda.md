# Eigenmodules of linear endomaps of left modules over commutative rings

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

open import linear-algebra.difference-linear-maps-left-modules-commutative-rings
open import linear-algebra.kernels-linear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.left-submodules-commutative-rings
open import linear-algebra.linear-endomaps-left-modules-commutative-rings
open import linear-algebra.scalar-multiplication-linear-maps-left-modules-commutative-rings
open import linear-algebra.subsets-left-modules-commutative-rings
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

  eigenmodule-linear-endo-left-module-Commutative-Ring :
    left-submodule-Commutative-Ring l2 R M
  eigenmodule-linear-endo-left-module-Commutative-Ring =
    kernel-linear-map-left-module-Commutative-Ring R M M
      ( diff-linear-map-left-module-Commutative-Ring R M M
        ( f)
        ( linear-endo-mul-left-module-Commutative-Ring R M r))

  subset-eigenmodule-linear-endo-left-module-Commutative-Ring :
    subset-left-module-Commutative-Ring l2 R M
  subset-eigenmodule-linear-endo-left-module-Commutative-Ring =
    subset-left-submodule-Commutative-Ring
      ( R)
      ( M)
      ( eigenmodule-linear-endo-left-module-Commutative-Ring)

  left-module-eigenmodule-linear-endo-left-module-Commutative-Ring :
    left-module-Commutative-Ring l2 R
  left-module-eigenmodule-linear-endo-left-module-Commutative-Ring =
    left-module-left-submodule-Commutative-Ring
      ( R)
      ( M)
      ( eigenmodule-linear-endo-left-module-Commutative-Ring)
```

## See also

- [Eigenspaces of linear endomaps of vector spaces](spectral-theory.eigenspaces-linear-endomaps-vector-spaces.md)

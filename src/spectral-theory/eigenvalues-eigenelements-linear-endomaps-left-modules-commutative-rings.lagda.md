# Eigenvalues and eigenelements of linear endomaps of left modules over commutative rings

```agda
module spectral-theory.eigenvalues-eigenelements-linear-endomaps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.left-submodules-commutative-rings
open import linear-algebra.linear-endomaps-left-modules-commutative-rings

open import spectral-theory.eigenmodules-linear-endomaps-left-modules-commutative-rings
```

</details>

## Idea

Given a
[linear endomap](linear-algebra.linear-endomaps-left-modules-commutative-rings.md)
`f` on a [left module](linear-algebra.left-modules-commutative-rings.md) `M`
over a [commutative ring](commutative-algebra.commutative-rings.md) `R`, an
element `v : M` is an
{{#concept "eigenelement" Disambiguation="of a linear endomap of a left module over a commutative ring"}}
of `f` with
{{#concept "eigenvalue" Disambiguation="of a linear endomap of a left module over a commutative ring"}}
`c : R` is an element of the
[eigenmodule](spectral-theory.eigenmodules-linear-endomaps-left-modules-commutative-rings.md)
associated with `c`, that is, an element of the
[kernel](linear-algebra.kernels-linear-maps-left-modules-commutative-rings.md)
of the map `v ↦ (f v - c * v)`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  where

  is-eigenelement-eigenvalue-prop-linear-endo-left-module-Commutative-Ring :
    type-Commutative-Ring R → type-left-module-Commutative-Ring R M → Prop l2
  is-eigenelement-eigenvalue-prop-linear-endo-left-module-Commutative-Ring =
    subset-eigenmodule-linear-endo-left-module-Commutative-Ring R M f

  is-eigenelement-eigenvalue-linear-endo-left-module-Commutative-Ring :
    type-Commutative-Ring R → type-left-module-Commutative-Ring R M → UU l2
  is-eigenelement-eigenvalue-linear-endo-left-module-Commutative-Ring c v =
    type-Prop
      ( is-eigenelement-eigenvalue-prop-linear-endo-left-module-Commutative-Ring
        ( c)
        ( v))
```

## Properties

### Zero is an eigenelement with every eigenvalue

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  where

  abstract
    is-eigenelement-zero-linear-endo-left-module-Commutative-Ring :
      (r : type-Commutative-Ring R) →
      is-eigenelement-eigenvalue-linear-endo-left-module-Commutative-Ring
        ( R)
        ( M)
        ( f)
        ( r)
        ( zero-left-module-Commutative-Ring R M)
    is-eigenelement-zero-linear-endo-left-module-Commutative-Ring r =
      contains-zero-left-submodule-Commutative-Ring R M
        ( eigenmodule-linear-endo-left-module-Commutative-Ring R M f r)
```

## See also

- [Eigenvalues and eigenvectors of vector spaces](spectral-theory.eigenvalues-eigenvectors-linear-endomaps-vector-spaces.md)

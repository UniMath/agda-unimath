# Eigenvalues and eigenelements of linear endomaps of left modules over rings

```agda
module spectral-theory.eigenvalues-eigenelements-linear-endomaps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-endomaps-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

Given a [linear endomap](linear-algebra.linear-endomaps-left-modules-rings.md)
`f` on a [left module](linear-algebra.left-modules-rings.md) `M` over a
[ring](ring-theory.rings.md) `R`, an element `x : M` is an
{{#concept "eigenelement" Disambiguation="of a linear endomap of a left module over a ring"}}
of `f` with
{{#concept "eigenvalue" Disambiguation="of a linear endomap of a left module over a ring"}}
`r : R` if `f x = r * x`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (f : linear-endo-left-module-Ring R M)
  where

  is-eigenelement-eigenvalue-prop-linear-endo-left-module-Ring :
    type-Ring R → type-left-module-Ring R M → Prop l2
  is-eigenelement-eigenvalue-prop-linear-endo-left-module-Ring r x =
    Id-Prop
      ( set-left-module-Ring R M)
      ( map-linear-endo-left-module-Ring R M f x)
      ( mul-left-module-Ring R M r x)

  is-eigenelement-eigenvalue-linear-endo-left-module-Ring :
    type-Ring R → type-left-module-Ring R M → UU l2
  is-eigenelement-eigenvalue-linear-endo-left-module-Ring r x =
    type-Prop
      ( is-eigenelement-eigenvalue-prop-linear-endo-left-module-Ring r x)
```

## Properties

### Zero is an eigenelement with every eigenvalue

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (f : linear-endo-left-module-Ring R M)
  where

  abstract
    is-eigenelement-zero-linear-endo-left-module-Ring :
      (r : type-Ring R) →
      is-eigenelement-eigenvalue-linear-endo-left-module-Ring
        ( R)
        ( M)
        ( f)
        ( r)
        ( zero-left-module-Ring R M)
    is-eigenelement-zero-linear-endo-left-module-Ring r =
      equational-reasoning
        map-linear-endo-left-module-Ring R M f (zero-left-module-Ring R M)
        ＝ zero-left-module-Ring R M
          by is-zero-map-zero-linear-endo-left-module-Ring R M f
        ＝ mul-left-module-Ring R M r (zero-left-module-Ring R M)
          by inv (right-zero-law-mul-left-module-Ring R M r)
```

## See also

- [Eigenvalues and eigenvectors of linear endomaps on left modules over commutative rings](spectral-theory.eigenvalues-eigenelements-linear-endomaps-left-modules-commutative-rings.md)
- [Eigenvalues and eigenvectors of linear endomaps on vector spaces](spectral-theory.eigenvalues-eigenvectors-linear-endomaps-vector-spaces.md)

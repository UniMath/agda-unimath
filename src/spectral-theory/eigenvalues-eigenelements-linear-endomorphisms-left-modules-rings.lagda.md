# Eigenvalues and eigenelements of linear transformations of left modules over rings

```agda
module spectral-theory.eigenvalues-eigenelements-linear-endomorphisms-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-endomorphisms-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

Given a
[linear endomorphism](linear-algebra.linear-endomorphisms-left-modules-rings.md)
`f` on a [left module](linear-algebra.left-modules-rings.md) `M` over a
[ring](ring-theory.rings.md) `R`, an element `x : M` is an
{{#concept "eigenelement" Disambiguation="of a linear transformation of a left module over a ring"}}
of `f` with
{{#concept "eigenvalue" Disambiguation="of a linear transformation of a left module over a ring"}}
`r : R` if `f x = r * x`.

We adopt the convention that the zero of `M` is an eigenelement with every
eigenvalue by default, because different modules will need different mechanisms
(e.g. [apartness relations](foundation.apartness-relations.md)) to
constructively describe nonzero elements.

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

- [Eigenvalues and eigenvectors of linear endomorphisms on left modules over commutative rings](spectral-theory.eigenvalues-eigenelements-linear-endomorphisms-left-modules-commutative-rings.md)
- [Eigenvalues and eigenvectors of linear endomorphisms on vector spaces](spectral-theory.eigenvalues-eigenvectors-linear-endomorphisms-vector-spaces.md)

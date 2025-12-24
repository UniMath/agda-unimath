# Eigenvalues and eigenvectors of linear transformations of vector spaces

```agda
module spectral-theory.eigenvalues-eigenvectors-linear-transformations-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-transformations-vector-spaces
open import linear-algebra.vector-spaces

open import spectral-theory.eigenvalues-eigenelements-linear-transformations-left-modules-rings
```

</details>

## Idea

Given a
[linear transformation](linear-algebra.linear-transformations-vector-spaces.md)
`f` on a [vector space](linear-algebra.vector-spaces.md) `V` over a
[Heyting field](commutative-algebra.heyting-fields.md) `F`, an vector `v : V` is
an
{{#concept "eigenvector" WDID=Q3555174 WD="eigenvector" Disambiguation="of a linear transformation of a vector space"}}
of `f` with
{{#concept "eigenvalue" WDID=Q3553768 WD="eigenvalue" Disambiguation="of a linear transformation of a vector space"}}
`c : F` if `f v = c * v`.

We adopt the convention that the zero of `V` is an eigenvector with every
eigenvalue by default, because different vector spaces will need different
mechanisms (e.g. [apartness relations](foundation.apartness-relations.md)) to
constructively describe nonzero vectors.

## Definition

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-transform-Vector-Space F V)
  where

  is-eigenvector-eigenvalue-prop-linear-transform-Vector-Space :
    type-Heyting-Field F → type-Vector-Space F V → Prop l2
  is-eigenvector-eigenvalue-prop-linear-transform-Vector-Space =
    is-eigenelement-eigenvalue-prop-linear-transform-left-module-Ring
      ( ring-Heyting-Field F)
      ( V)
      ( f)

  is-eigenvector-eigenvalue-linear-transform-Vector-Space :
    type-Heyting-Field F → type-Vector-Space F V → UU l2
  is-eigenvector-eigenvalue-linear-transform-Vector-Space c v =
    type-Prop (is-eigenvector-eigenvalue-prop-linear-transform-Vector-Space c v)
```

## See also

- [Eigenvalues and eigenelements of left modules over rings](spectral-theory.eigenvalues-eigenelements-linear-transformations-left-modules-rings.md)
- [Eigenvalues and eigenelements of left modules over commutative rings](spectral-theory.eigenvalues-eigenelements-linear-transformations-left-modules-commutative-rings.md)

## External links

- [Eigenvalues and eigenvectors](https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors)
  on Wikipedia

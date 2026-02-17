# Eigenvalues and eigenvectors of linear endomaps of vector spaces

```agda
module spectral-theory.eigenvalues-eigenvectors-linear-endomaps-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-endomaps-vector-spaces
open import linear-algebra.vector-spaces

open import spectral-theory.eigenvalues-eigenelements-linear-endomaps-left-modules-commutative-rings
```

</details>

## Idea

Given a [linear endomap](linear-algebra.linear-endomaps-vector-spaces.md) `f` on
a [vector space](linear-algebra.vector-spaces.md) `V` over a
[Heyting field](commutative-algebra.heyting-fields.md) `F`, an vector `v : V` is
an
{{#concept "eigenvector" WDID=Q3555174 WD="eigenvector" Disambiguation="of a linear endomap of a vector space"}}
of `f` with
{{#concept "eigenvalue" WDID=Q3553768 WD="eigenvalue" Disambiguation="of a linear endomap of a vector space"}}
`c : F` if it is a member of the
[eigenspace](spectral-theory.eigenspaces-linear-endomaps-vector-spaces.md)
associated with `c`, that is, it is in the kernel of the map `v ↦ (f v - c * v)`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-endo-Vector-Space F V)
  where

  is-eigenvector-eigenvalue-prop-linear-endo-Vector-Space :
    type-Heyting-Field F → type-Vector-Space F V → Prop l2
  is-eigenvector-eigenvalue-prop-linear-endo-Vector-Space =
    is-eigenelement-eigenvalue-prop-linear-endo-left-module-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( V)
      ( f)

  is-eigenvector-eigenvalue-linear-endo-Vector-Space :
    type-Heyting-Field F → type-Vector-Space F V → UU l2
  is-eigenvector-eigenvalue-linear-endo-Vector-Space c v =
    type-Prop (is-eigenvector-eigenvalue-prop-linear-endo-Vector-Space c v)
```

## See also

- [Eigenvalues and eigenelements of left modules over commutative rings](spectral-theory.eigenvalues-eigenelements-linear-endomaps-left-modules-commutative-rings.md)

## External links

- [Eigenvalues and eigenvectors](https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors)
  on Wikipedia

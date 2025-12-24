# Eigenspaces of linear transformations of vector spaces

```agda
module spectral-theory.eigenspaces-linear-transformations-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.linear-transformations-vector-spaces
open import linear-algebra.subspaces-vector-spaces
open import linear-algebra.vector-spaces

open import spectral-theory.eigenmodules-linear-transformations-left-modules-commutative-rings
```

</details>

## Idea

Given a
[linear transformation](linear-algebra.linear-transformations-vector-spaces.md)
`f` of a [vector space](linear-algebra.vector-spaces.md) `V` over a
[Heyting field](commutative-algebra.heyting-fields.md) `F`, the
{{#concept "eigenspace" WDID=Q1303223 WD="eigenspace" Disambiguation="of a linear transformation on a vector space" Agda=eigenspace-linear-transform-Vector-Space}}
of `c : F` is the [subspace](linear-algebra.subspaces-vector-spaces.md) of `V`
of vectors with
[eigenvalue](spectral-theory.eigenvalues-eigenvectors-linear-transformations-vector-spaces.md)
`c`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-transform-Vector-Space F V)
  (c : type-Heyting-Field F)
  where

  eigenspace-linear-transform-Vector-Space : subspace-Vector-Space l2 F V
  eigenspace-linear-transform-Vector-Space =
    eigenmodule-linear-transform-left-module-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( V)
      ( f)
      ( c)

  vector-space-eigenspace-linear-transform-Vector-Space : Vector-Space l2 F
  vector-space-eigenspace-linear-transform-Vector-Space =
    left-eigenmodule-linear-transform-left-module-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( V)
      ( f)
      ( c)
```

## See also

- [Eigenmodules of linear transformations of left modules over commutative rings](spectral-theory.eigenmodules-linear-transformations-left-modules-commutative-rings.md)

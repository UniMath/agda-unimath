# Eigenspaces of linear endomaps of vector spaces

```agda
module spectral-theory.eigenspaces-linear-endomaps-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.linear-endomaps-vector-spaces
open import linear-algebra.subspaces-vector-spaces
open import linear-algebra.vector-spaces

open import spectral-theory.eigenmodules-linear-endomaps-left-modules-commutative-rings
```

</details>

## Idea

Given a [linear endomaps](linear-algebra.linear-endomaps-vector-spaces.md) `f`
of a [vector space](linear-algebra.vector-spaces.md) `V` over a
[Heyting field](commutative-algebra.heyting-fields.md) `F`, the
{{#concept "eigenspace" WDID=Q1303223 WD="eigenspace" Disambiguation="of a linear endomap on a vector space" Agda=eigenspace-linear-endo-Vector-Space}}
of `c : F` is the [subspace](linear-algebra.subspaces-vector-spaces.md) of `V`
of vectors with
[eigenvalue](spectral-theory.eigenvalues-eigenvectors-linear-endomaps-vector-spaces.md)
`c`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-endo-Vector-Space F V)
  (c : type-Heyting-Field F)
  where

  eigenspace-linear-endo-Vector-Space : subspace-Vector-Space l2 F V
  eigenspace-linear-endo-Vector-Space =
    eigenmodule-linear-endo-left-module-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( V)
      ( f)
      ( c)

  vector-space-eigenspace-linear-endo-Vector-Space : Vector-Space l2 F
  vector-space-eigenspace-linear-endo-Vector-Space =
    left-eigenmodule-linear-endo-left-module-Commutative-Ring
      ( commutative-ring-Heyting-Field F)
      ( V)
      ( f)
      ( c)
```

## See also

- [Eigenmodules of linear transformations of left modules over commutative rings](spectral-theory.eigenmodules-linear-endomaps-left-modules-commutative-rings.md)

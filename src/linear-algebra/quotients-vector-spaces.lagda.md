# Quotients of vector spaces

```agda
module linear-algebra.quotients-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.universe-levels

open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.quotients-left-modules-rings
open import linear-algebra.subspaces-vector-spaces
open import linear-algebra.vector-spaces
```

</details>

## Idea

Given a [vector space](linear-algebra.vector-spaces.md) `V` over a
[Heyting field](commutative-algebra.heyting-fields.md) `K` and a
[subspace](linear-algebra.subspaces-vector-spaces.md) `W` of `V`, the
{{#concept "quotient space" WDID=Q1393796 WD="quotient space" Disambiguation="of a vector space over a Heyting field" Agda=quotient-Vector-Space}}
`V/W` is the [quotient](linear-algebra.quotients-left-modules-rings.md) of `V`
and `W` interpreted as [left modules](linear-algebra.left-modules-rings.md) over
`K`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  (W : subspace-Vector-Space l3 K V)
  where

  quotient-Vector-Space : Vector-Space (l2 ⊔ l3) K
  quotient-Vector-Space = quotient-left-module-Ring (ring-Heyting-Field K) V W

  type-quotient-Vector-Space : UU (l2 ⊔ l3)
  type-quotient-Vector-Space = type-Vector-Space K quotient-Vector-Space

  linear-map-quotient-Vector-Space :
    linear-map-Vector-Space K V quotient-Vector-Space
  linear-map-quotient-Vector-Space =
    linear-map-quotient-left-module-Ring (ring-Heyting-Field K) V W

  map-quotient-Vector-Space : type-Vector-Space K V → type-quotient-Vector-Space
  map-quotient-Vector-Space =
    map-quotient-hom-left-module-Ring (ring-Heyting-Field K) V W
```

## External links

- [Quotient space (linear algebra)](<https://en.wikipedia.org/wiki/Quotient_space_(linear_algebra)>)
  on Wikipedia

# Isomorphisms of vector spaces

```agda
module linear-algebra.isomorphisms-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.isomorphisms-left-modules-rings
open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.vector-spaces
```

</details>

## Idea

{{#concept "Isomorphisms" Disambiguation="of left modules over a commutative ring" Agda=iso-Vector-Space}}
of [vector spaces](linear-algebra.vector-spaces.md) are
[linear maps](linear-algebra.linear-maps-vector-spaces.md) that have a two-sided
inverse.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Heyting-Field l1)
  (M : Vector-Space l2 R)
  (N : Vector-Space l3 R)
  where

  is-iso-prop-Vector-Space :
    subtype (l1 ⊔ l2 ⊔ l3) (linear-map-Vector-Space R M N)
  is-iso-prop-Vector-Space =
    is-iso-prop-left-module-Ring (ring-Heyting-Field R) M N

  is-iso-Vector-Space :
    linear-map-Vector-Space R M N → UU (l1 ⊔ l2 ⊔ l3)
  is-iso-Vector-Space =
    is-in-subtype is-iso-prop-Vector-Space

  iso-Vector-Space : UU (l1 ⊔ l2 ⊔ l3)
  iso-Vector-Space =
    type-subtype is-iso-prop-Vector-Space

  linear-map-iso-Vector-Space :
    iso-Vector-Space →
    linear-map-Vector-Space R M N
  linear-map-iso-Vector-Space = pr1

  is-iso-linear-map-iso-Vector-Space :
    (i : iso-Vector-Space) →
    is-iso-Vector-Space
      ( linear-map-iso-Vector-Space i)
  is-iso-linear-map-iso-Vector-Space = pr2

module _
  {l1 l2 l3 : Level}
  (R : Heyting-Field l1)
  (M : Vector-Space l2 R)
  (N : Vector-Space l3 R)
  (f : iso-Vector-Space R M N)
  where

  inv-iso-Vector-Space : iso-Vector-Space R N M
  inv-iso-Vector-Space =
    inv-iso-left-module-Ring (ring-Heyting-Field R) M N f

  linear-map-inv-iso-Vector-Space :
    linear-map-Vector-Space R N M
  linear-map-inv-iso-Vector-Space =
    linear-map-inv-iso-left-module-Ring (ring-Heyting-Field R) M N f
```

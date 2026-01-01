# Bilinear maps on vector spaces

```agda
module linear-algebra.bilinear-maps-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.bilinear-maps-left-modules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

A
{{#concept "bilinear map" WDID=Q1086961 WD="bilinear map" Disambiguation="from two vector spaces to a third" Agda=bilinear-map-Vector-Space}}
from two [vector spaces](linear-algebra.vector-spaces.md) `X` and `Y` over a
[Heyting field](commutative-algebra.heyting-fields.md) `F` to a third vector
space `Z` is a map `f : X → Y → Z` which is
[linear](linear-algebra.linear-maps-vector-spaces.md) in each argument.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F : Heyting-Field l1)
  (X : Vector-Space l2 F)
  (Y : Vector-Space l3 F)
  (Z : Vector-Space l4 F)
  (f :
    type-Vector-Space F X → type-Vector-Space F Y →
    type-Vector-Space F Z)
  where

  is-linear-on-left-prop-bimap-Vector-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-left-prop-bimap-Vector-Space =
    is-linear-on-left-prop-bimap-left-module-Ring
      ( ring-Heyting-Field F)
      ( X)
      ( Y)
      ( Z)
      ( f)

  is-linear-on-left-bimap-Vector-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-left-bimap-Vector-Space =
    type-Prop is-linear-on-left-prop-bimap-Vector-Space

  is-linear-on-right-prop-bimap-Vector-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-right-prop-bimap-Vector-Space =
    is-linear-on-right-prop-bimap-left-module-Ring
      ( ring-Heyting-Field F)
      ( X)
      ( Y)
      ( Z)
      ( f)

  is-linear-on-right-bimap-Vector-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-linear-on-right-bimap-Vector-Space =
    type-Prop is-linear-on-right-prop-bimap-Vector-Space

  is-bilinear-map-prop-Vector-Space : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-bilinear-map-prop-Vector-Space =
    is-bilinear-map-prop-left-module-Ring
      ( ring-Heyting-Field F)
      ( X)
      ( Y)
      ( Z)
      ( f)

  is-bilinear-map-Vector-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-bilinear-map-Vector-Space =
    type-Prop is-bilinear-map-prop-Vector-Space

bilinear-map-Vector-Space :
  {l1 l2 l3 l4 : Level} (F : Heyting-Field l1) →
  Vector-Space l2 F → Vector-Space l3 F → Vector-Space l4 F →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
bilinear-map-Vector-Space F X Y Z =
  type-subtype (is-bilinear-map-prop-Vector-Space F X Y Z)

module _
  {l1 l2 l3 l4 : Level}
  (F : Heyting-Field l1)
  (X : Vector-Space l2 F)
  (Y : Vector-Space l3 F)
  (Z : Vector-Space l4 F)
  (f : bilinear-map-Vector-Space F X Y Z)
  where

  map-bilinear-map-Vector-Space :
    type-Vector-Space F X → type-Vector-Space F Y → type-Vector-Space F Z
  map-bilinear-map-Vector-Space = pr1 f
```

## See also

- [Bilinear maps on left modules over rings](linear-algebra.bilinear-maps-left-modules-rings.md)
- [Bilinear maps on left modules over commutative rings](linear-algebra.bilinear-maps-left-modules-commutative-rings.md)

## External links

- [Bilinear map](https://en.wikipedia.org/wiki/Bilinear_map) on Wikipedia

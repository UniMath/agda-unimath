# Linear maps on vector spaces

```agda
module linear-algebra.linear-maps-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

A
{{#concept "linear map" Disambiguation="between vector spaces" WDID=Q207643 WD="linear map" Disambiguation=linear-map-Vector-Space}}
from a [vector space](linear-algebra.vector-spaces.md) `V` over a
[Heyting field](commutative-algebra.heyting-fields.md) `F` to another vector
space `W` over `F` is a
[linear map](linear-algebra.linear-maps-left-modules-rings.md) from `V` as a
[left module](linear-algebra.left-modules-rings.md) over the
[ring](ring-theory.rings.md) associated with `F` to `W` as the corresponding
left module.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  (f : type-Vector-Space F V → type-Vector-Space F W)
  where

  is-additive-map-prop-Vector-Space : Prop (l2 ⊔ l3)
  is-additive-map-prop-Vector-Space =
    is-additive-map-prop-left-module-Ring
      ( ring-Heyting-Field F)
      ( V)
      ( W)
      ( f)

  is-additive-map-Vector-Space : UU (l2 ⊔ l3)
  is-additive-map-Vector-Space = type-Prop is-additive-map-prop-Vector-Space

  is-homogeneous-map-prop-Vector-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-homogeneous-map-prop-Vector-Space =
    is-homogeneous-map-prop-left-module-Ring
      ( ring-Heyting-Field F)
      ( V)
      ( W)
      ( f)

  is-homogeneous-map-Vector-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-homogeneous-map-Vector-Space =
    type-Prop is-homogeneous-map-prop-Vector-Space

  is-linear-map-prop-Vector-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-linear-map-prop-Vector-Space =
    is-linear-map-prop-left-module-Ring
      ( ring-Heyting-Field F)
      ( V)
      ( W)
      ( f)

  is-linear-map-Vector-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-linear-map-Vector-Space = type-Prop is-linear-map-prop-Vector-Space

linear-map-Vector-Space :
  {l1 l2 l3 : Level} (F : Heyting-Field l1) →
  Vector-Space l2 F → Vector-Space l3 F → UU (l1 ⊔ l2 ⊔ l3)
linear-map-Vector-Space F V W =
  type-subtype (is-linear-map-prop-Vector-Space F V W)

module _
  {l1 l2 l3 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  (f : linear-map-Vector-Space F V W)
  where

  map-linear-map-Vector-Space : type-Vector-Space F V → type-Vector-Space F W
  map-linear-map-Vector-Space = pr1 f

  is-linear-map-linear-map-Vector-Space :
    is-linear-map-Vector-Space F V W map-linear-map-Vector-Space
  is-linear-map-linear-map-Vector-Space = pr2 f

  is-additive-map-linear-map-Vector-Space :
    is-additive-map-Vector-Space F V W map-linear-map-Vector-Space
  is-additive-map-linear-map-Vector-Space =
    pr1 is-linear-map-linear-map-Vector-Space

  is-homogeneous-map-linear-map-Vector-Space :
    is-homogeneous-map-Vector-Space F V W map-linear-map-Vector-Space
  is-homogeneous-map-linear-map-Vector-Space =
    pr2 is-linear-map-linear-map-Vector-Space
```

## Properties

### A linear map maps zero to zero

```agda
module _
  {l1 l2 l3 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  (f : linear-map-Vector-Space F V W)
  where

  abstract
    is-zero-map-zero-linear-map-Vector-Space :
      is-zero-Vector-Space F W
        ( map-linear-map-Vector-Space F V W f (zero-Vector-Space F V))
    is-zero-map-zero-linear-map-Vector-Space =
      is-zero-map-zero-linear-map-left-module-Ring
        ( ring-Heyting-Field F)
        ( V)
        ( W)
        ( f)
```

### A linear map maps `-v` to the negation of the map of `v`

```agda
module _
  {l1 l2 l3 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  (f : linear-map-Vector-Space F V W)
  where

  abstract
    map-neg-linear-map-Vector-Space :
      (v : type-Vector-Space F V) →
      map-linear-map-Vector-Space F V W f (neg-Vector-Space F V v) ＝
      neg-Vector-Space F W (map-linear-map-Vector-Space F V W f v)
    map-neg-linear-map-Vector-Space =
      map-neg-linear-map-left-module-Ring
        ( ring-Heyting-Field F)
        ( V)
        ( W)
        ( f)
```

### The composition of linear maps is linear

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  (X : Vector-Space l4 F)
  (g : type-Vector-Space F W → type-Vector-Space F X)
  (f : type-Vector-Space F V → type-Vector-Space F W)
  where

  abstract
    is-linear-comp-is-linear-map-Vector-Space :
      is-linear-map-Vector-Space F W X g →
      is-linear-map-Vector-Space F V W f →
      is-linear-map-Vector-Space F V X (g ∘ f)
    is-linear-comp-is-linear-map-Vector-Space =
      is-linear-comp-is-linear-map-left-module-Ring
        ( ring-Heyting-Field F)
        ( V)
        ( W)
        ( X)
        ( g)
        ( f)
```

### The linear composition of linear maps between vector spaces

```agda
module _
  {l1 l2 l3 l4 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  (X : Vector-Space l4 F)
  (g : linear-map-Vector-Space F W X)
  (f : linear-map-Vector-Space F V W)
  where

  comp-linear-map-Vector-Space : linear-map-Vector-Space F V X
  comp-linear-map-Vector-Space =
    comp-linear-map-left-module-Ring
      ( ring-Heyting-Field F)
      ( V)
      ( W)
      ( X)
      ( g)
      ( f)
```

## External links

- [Linear maps](https://en.wikipedia.org/wiki/Linear_map) on Wikipedia

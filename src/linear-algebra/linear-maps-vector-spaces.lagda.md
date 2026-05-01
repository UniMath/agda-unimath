# Linear maps on vector spaces

```agda
module linear-algebra.linear-maps-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
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

module _
  {l1 l2 l3 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (W : Vector-Space l3 F)
  where

  hom-set-Vector-Space : Set (l1 ⊔ l2 ⊔ l3)
  hom-set-Vector-Space =
    set-subset
      ( hom-set-Set (set-Vector-Space F V) (set-Vector-Space F W))
      ( is-linear-map-prop-Vector-Space F V W)

  linear-map-Vector-Space : UU (l1 ⊔ l2 ⊔ l3)
  linear-map-Vector-Space = type-Set hom-set-Vector-Space

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
    is-linear-map-comp-Vector-Space :
      is-linear-map-Vector-Space F W X g →
      is-linear-map-Vector-Space F V W f →
      is-linear-map-Vector-Space F V X (g ∘ f)
    is-linear-map-comp-Vector-Space =
      is-linear-map-comp-left-module-Ring
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

### The identity linear map from a vector space to itself

```agda
module _
  {l1 l2 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  where

  id-linear-map-Vector-Space : linear-map-Vector-Space K V V
  id-linear-map-Vector-Space =
    id-linear-map-left-module-Ring (ring-Heyting-Field K) V
```

### Homotopy characterizes equality of linear maps

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  (W : Vector-Space l3 K)
  where

  htpy-linear-map-Vector-Space :
    Relation (l2 ⊔ l3) (linear-map-Vector-Space K V W)
  htpy-linear-map-Vector-Space =
    htpy-linear-map-left-module-Ring (ring-Heyting-Field K) V W

  abstract
    eq-htpy-linear-map-Vector-Space :
      (f g : linear-map-Vector-Space K V W) →
      htpy-linear-map-Vector-Space f g → f ＝ g
    eq-htpy-linear-map-Vector-Space =
      eq-htpy-linear-map-left-module-Ring (ring-Heyting-Field K) V W
```

### Associativity of composition of linear maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (K : Heyting-Field l1)
  (M : Vector-Space l2 K)
  (N : Vector-Space l3 K)
  (P : Vector-Space l4 K)
  (Q : Vector-Space l5 K)
  where

  abstract
    associative-comp-linear-map-Vector-Space :
      (f : linear-map-Vector-Space K P Q)
      (g : linear-map-Vector-Space K N P)
      (h : linear-map-Vector-Space K M N) →
      comp-linear-map-Vector-Space K M N Q
        ( comp-linear-map-Vector-Space K N P Q f g)
        ( h) ＝
      comp-linear-map-Vector-Space K M P Q
        ( f)
        ( comp-linear-map-Vector-Space K M N P g h)
    associative-comp-linear-map-Vector-Space =
      associative-comp-linear-map-left-module-Ring
        ( ring-Heyting-Field K)
        ( M)
        ( N)
        ( P)
        ( Q)
```

### Unit laws of composition of linear maps

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (M : Vector-Space l2 K)
  (N : Vector-Space l3 K)
  where

  abstract
    left-unit-law-comp-linear-map-Vector-Space :
      (f : linear-map-Vector-Space K M N) →
      comp-linear-map-Vector-Space K M N N
        ( id-linear-map-Vector-Space K N)
        ( f) ＝
      f
    left-unit-law-comp-linear-map-Vector-Space =
      left-unit-law-comp-linear-map-left-module-Ring (ring-Heyting-Field K) M N

    right-unit-law-comp-linear-map-Vector-Space :
      (f : linear-map-Vector-Space K M N) →
      comp-linear-map-Vector-Space K M M N
        ( f)
        ( id-linear-map-Vector-Space K M) ＝
      f
    right-unit-law-comp-linear-map-Vector-Space =
      right-unit-law-comp-linear-map-left-module-Ring (ring-Heyting-Field K) M N
```

## External links

- [Linear maps](https://en.wikipedia.org/wiki/Linear_map) on Wikipedia

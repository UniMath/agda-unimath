# Linear transformations on vector spaces

```agda
module linear-algebra.linear-transformations-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.linear-transformations-left-modules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

A
{{#concept "linear transformation" Disambiguation="on vector spaces" Agda=linear-transform-Vector-Space}}
on a [vector space](linear-algebra.vector-spaces.md) `V` is a
[linear map](linear-algebra.linear-maps-vector-spaces.md) from `V` to itself.

## Definition

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  where

  is-linear-transform-prop-Vector-Space :
    (type-Vector-Space F V → type-Vector-Space F V) → Prop (l1 ⊔ l2)
  is-linear-transform-prop-Vector-Space =
    is-linear-map-prop-Vector-Space F V V

  is-linear-transform-Vector-Space :
    (type-Vector-Space F V → type-Vector-Space F V) → UU (l1 ⊔ l2)
  is-linear-transform-Vector-Space f =
    type-Prop (is-linear-transform-prop-Vector-Space f)

  linear-transform-Vector-Space : UU (l1 ⊔ l2)
  linear-transform-Vector-Space =
    type-subtype is-linear-transform-prop-Vector-Space

module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-transform-Vector-Space F V)
  where

  map-linear-transform-Vector-Space :
    type-Vector-Space F V → type-Vector-Space F V
  map-linear-transform-Vector-Space = pr1 f

  is-linear-transform-map-linear-transform-Vector-Space :
    is-linear-transform-Vector-Space F V map-linear-transform-Vector-Space
  is-linear-transform-map-linear-transform-Vector-Space = pr2 f
```

## Properties

### A linear transformation maps zero to zero

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-transform-Vector-Space F V)
  where

  abstract
    is-zero-map-zero-linear-transform-Vector-Space :
      is-zero-Vector-Space F V
        ( map-linear-transform-Vector-Space F V f (zero-Vector-Space F V))
    is-zero-map-zero-linear-transform-Vector-Space =
      is-zero-map-zero-linear-map-Vector-Space F V V f
```

### A linear map maps `-v` to the negation of the map of `v`

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-transform-Vector-Space F V)
  where

  abstract
    map-neg-linear-transform-Vector-Space :
      (v : type-Vector-Space F V) →
      map-linear-transform-Vector-Space F V f (neg-Vector-Space F V v) ＝
      neg-Vector-Space F V (map-linear-transform-Vector-Space F V f v)
    map-neg-linear-transform-Vector-Space =
      map-neg-linear-map-Vector-Space F V V f
```

### The identity map is a linear transformation

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  where

  is-linear-map-id-Vector-Space : is-linear-transform-Vector-Space F V id
  is-linear-id-Vector-Space =
    is-linear-id-left-module-Ring (ring-Heyting-Field F) V

  id-linear-transform-Vector-Space : linear-transform-Vector-Space F V
  id-linear-transform-Vector-Space =
    id-linear-transform-left-module-Ring (ring-Heyting-Field F) V
```

### The composition of linear transformations is a linear transformation

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (g : type-Vector-Space F V → type-Vector-Space F V)
  (f : type-Vector-Space F V → type-Vector-Space F V)
  where

  abstract
    is-linear-transform-comp-is-linear-transform-Vector-Space :
      is-linear-transform-Vector-Space F V g →
      is-linear-transform-Vector-Space F V f →
      is-linear-transform-Vector-Space F V (g ∘ f)
    is-linear-transform-comp-is-linear-transform-Vector-Space =
      is-linear-comp-is-linear-map-Vector-Space F V V V g f
```

### The linear composition of linear transformations

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (g : linear-transform-Vector-Space F V)
  (f : linear-transform-Vector-Space F V)
  where

  comp-linear-transform-Vector-Space : linear-transform-Vector-Space F V
  comp-linear-transform-Vector-Space =
    comp-linear-map-Vector-Space F V V V g f
```

### Iterating linear transformations

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  where

  abstract
    is-linear-transform-iterate-map-linear-transform-Vector-Space :
      (n : ℕ) (f : linear-transform-Vector-Space F V) →
      is-linear-transform-Vector-Space F V
        ( iterate n (map-linear-transform-Vector-Space F V f))
    is-linear-transform-iterate-map-linear-transform-Vector-Space =
      is-linear-transform-iterate-map-linear-transform-left-module-Ring
        ( ring-Heyting-Field F)
        ( V)

  iterate-linear-transform-Vector-Space :
    ℕ → linear-transform-Vector-Space F V → linear-transform-Vector-Space F V
  iterate-linear-transform-Vector-Space =
    iterate-linear-transform-left-module-Ring (ring-Heyting-Field F) V
```

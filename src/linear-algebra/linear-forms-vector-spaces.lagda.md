# Linear forms in vector spaces

```agda
module linear-algebra.linear-forms-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.vector-spaces
```

</details>

## Idea

A
{{#concept "linear form" WDID=Q261527 WD="linear functional" Disambiguation="on vector spaces" Agda=linear-form-Vector-Space}}
on a [vector space](linear-algebra.vector-spaces.md) `V` over a
[Heyting field](commutative-algebra.heyting-fields.md) `F` is a
[linear map](linear-algebra.linear-maps-vector-spaces.md) from `V` to the vector
space of `F` over itself.

## Definition

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  where

  is-linear-form-prop-Vector-Space :
    (type-Vector-Space F V → type-Heyting-Field F) → Prop (l1 ⊔ l2)
  is-linear-form-prop-Vector-Space =
    is-linear-map-prop-Vector-Space
      ( F)
      ( V)
      ( vector-space-heyting-field-Heyting-Field F)

  is-linear-form-Vector-Space :
    (type-Vector-Space F V → type-Heyting-Field F) → UU (l1 ⊔ l2)
  is-linear-form-Vector-Space f = type-Prop (is-linear-form-prop-Vector-Space f)

  linear-form-Vector-Space : UU (l1 ⊔ l2)
  linear-form-Vector-Space = type-subtype is-linear-form-prop-Vector-Space

module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-form-Vector-Space F V)
  where

  map-linear-form-Vector-Space : type-Vector-Space F V → type-Heyting-Field F
  map-linear-form-Vector-Space = pr1 f

  is-linear-form-linear-form-Vector-Space :
    is-linear-form-Vector-Space F V map-linear-form-Vector-Space
  is-linear-form-linear-form-Vector-Space = pr2 f

  is-additive-map-linear-form-Vector-Space :
    (v w : type-Vector-Space F V) →
    map-linear-form-Vector-Space (add-Vector-Space F V v w) ＝
    add-Heyting-Field F
      ( map-linear-form-Vector-Space v)
      ( map-linear-form-Vector-Space w)
  is-additive-map-linear-form-Vector-Space =
    pr1 is-linear-form-linear-form-Vector-Space

  is-homogeneous-map-linear-form-Vector-Space :
    (c : type-Heyting-Field F) (v : type-Vector-Space F V) →
    map-linear-form-Vector-Space (mul-Vector-Space F V c v) ＝
    mul-Heyting-Field F c (map-linear-form-Vector-Space v)
  is-homogeneous-map-linear-form-Vector-Space =
    pr2 is-linear-form-linear-form-Vector-Space
```

## Properties

### A linear form maps zero to zero

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-form-Vector-Space F V)
  where

  abstract
    is-zero-map-zero-linear-form-Vector-Space :
      is-zero-Heyting-Field F
        ( map-linear-form-Vector-Space F V f (zero-Vector-Space F V))
    is-zero-map-zero-linear-form-Vector-Space =
      is-zero-map-zero-linear-map-Vector-Space
        ( F)
        ( V)
        ( vector-space-heyting-field-Heyting-Field F)
        ( f)
```

### A linear form maps `-v` to the negation of the map of `v`

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-form-Vector-Space F V)
  where

  abstract
    map-neg-linear-form-Vector-Space :
      (v : type-Vector-Space F V) →
      map-linear-form-Vector-Space F V f (neg-Vector-Space F V v) ＝
      neg-Heyting-Field F (map-linear-form-Vector-Space F V f v)
    map-neg-linear-form-Vector-Space =
      map-neg-linear-map-Vector-Space
        ( F)
        ( V)
        ( vector-space-heyting-field-Heyting-Field F)
        ( f)
```

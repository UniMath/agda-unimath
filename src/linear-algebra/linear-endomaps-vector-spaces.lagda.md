# Linear endomorphisms on vector spaces

```agda
module linear-algebra.linear-endomaps-vector-spaces where
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

open import linear-algebra.linear-endomaps-left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.vector-spaces
```

</details>

## Idea

A
{{#concept "linear endomorphism" Disambiguation="on vector spaces" Agda=linear-endo-Vector-Space}}
on a [vector space](linear-algebra.vector-spaces.md) `V` is a
[linear map](linear-algebra.linear-maps-vector-spaces.md) from `V` to itself.

## Definition

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  where

  is-linear-endo-prop-Vector-Space :
    (type-Vector-Space F V → type-Vector-Space F V) → Prop (l1 ⊔ l2)
  is-linear-endo-prop-Vector-Space =
    is-linear-map-prop-Vector-Space F V V

  is-linear-endo-Vector-Space :
    (type-Vector-Space F V → type-Vector-Space F V) → UU (l1 ⊔ l2)
  is-linear-endo-Vector-Space f =
    type-Prop (is-linear-endo-prop-Vector-Space f)

  linear-endo-Vector-Space : UU (l1 ⊔ l2)
  linear-endo-Vector-Space =
    type-subtype is-linear-endo-prop-Vector-Space

module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-endo-Vector-Space F V)
  where

  map-linear-endo-Vector-Space :
    type-Vector-Space F V → type-Vector-Space F V
  map-linear-endo-Vector-Space = pr1 f

  is-linear-endo-map-linear-endo-Vector-Space :
    is-linear-endo-Vector-Space F V map-linear-endo-Vector-Space
  is-linear-endo-map-linear-endo-Vector-Space = pr2 f
```

## Properties

### A linear endomorphism maps zero to zero

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-endo-Vector-Space F V)
  where

  abstract
    is-zero-map-zero-linear-endo-Vector-Space :
      is-zero-Vector-Space F V
        ( map-linear-endo-Vector-Space F V f (zero-Vector-Space F V))
    is-zero-map-zero-linear-endo-Vector-Space =
      is-zero-map-zero-linear-map-Vector-Space F V V f
```

### A linear endomorphism maps `-v` to the negation of the map of `v`

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (f : linear-endo-Vector-Space F V)
  where

  abstract
    map-neg-linear-endo-Vector-Space :
      (v : type-Vector-Space F V) →
      map-linear-endo-Vector-Space F V f (neg-Vector-Space F V v) ＝
      neg-Vector-Space F V (map-linear-endo-Vector-Space F V f v)
    map-neg-linear-endo-Vector-Space =
      map-neg-linear-map-Vector-Space F V V f
```

### The identity map is a linear endomorphism

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  where

  is-linear-map-id-Vector-Space : is-linear-endo-Vector-Space F V id
  is-linear-map-id-Vector-Space =
    is-linear-map-id-left-module-Ring (ring-Heyting-Field F) V

  id-linear-endo-Vector-Space : linear-endo-Vector-Space F V
  id-linear-endo-Vector-Space =
    id-linear-endo-left-module-Ring (ring-Heyting-Field F) V
```

### Composition of linear endomorphisms

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (g : type-Vector-Space F V → type-Vector-Space F V)
  (f : type-Vector-Space F V → type-Vector-Space F V)
  where

  abstract
    is-linear-endo-comp-Vector-Space :
      is-linear-endo-Vector-Space F V g →
      is-linear-endo-Vector-Space F V f →
      is-linear-endo-Vector-Space F V (g ∘ f)
    is-linear-endo-comp-Vector-Space =
      is-linear-map-comp-Vector-Space F V V V g f
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (g : linear-endo-Vector-Space F V)
  (f : linear-endo-Vector-Space F V)
  where

  comp-linear-endo-Vector-Space : linear-endo-Vector-Space F V
  comp-linear-endo-Vector-Space =
    comp-linear-map-Vector-Space F V V V g f
```

### Iterating linear endomorphisms

```agda
module _
  {l1 l2 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  where

  abstract
    is-linear-endo-iterate-map-linear-endo-Vector-Space :
      (n : ℕ) (f : linear-endo-Vector-Space F V) →
      is-linear-endo-Vector-Space F V
        ( iterate n (map-linear-endo-Vector-Space F V f))
    is-linear-endo-iterate-map-linear-endo-Vector-Space =
      is-linear-endo-iterate-map-linear-endo-left-module-Ring
        ( ring-Heyting-Field F)
        ( V)

  iterate-linear-endo-Vector-Space :
    ℕ → linear-endo-Vector-Space F V → linear-endo-Vector-Space F V
  iterate-linear-endo-Vector-Space =
    iterate-linear-endo-left-module-Ring (ring-Heyting-Field F) V
```

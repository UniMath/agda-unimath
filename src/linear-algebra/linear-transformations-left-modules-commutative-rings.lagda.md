# Linear transformations on left modules over commutative rings

```agda
module linear-algebra.linear-transformations-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.linear-transformations-left-modules-rings
```

</details>

## Idea

A
{{#concept "linear transformation" Disambiguation="on left modules over commutative rings" Agda=linear-transform-left-module-Commutative-Ring}}
on a [left module](linear-algebra.left-modules-commutative-rings.md) `M` over a
[commutative ring](commutative-algebra.commutative-rings.md) is a
[linear map](linear-algebra.linear-maps-left-modules-commutative-rings.md) from
`M` to itself.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  is-linear-transform-prop-left-module-Commutative-Ring :
    ( type-left-module-Commutative-Ring R M →
      type-left-module-Commutative-Ring R M) →
    Prop (l1 ⊔ l2)
  is-linear-transform-prop-left-module-Commutative-Ring =
    is-linear-map-prop-left-module-Commutative-Ring R M M

  is-linear-transform-left-module-Commutative-Ring :
    ( type-left-module-Commutative-Ring R M →
      type-left-module-Commutative-Ring R M) →
    UU (l1 ⊔ l2)
  is-linear-transform-left-module-Commutative-Ring f =
    type-Prop (is-linear-transform-prop-left-module-Commutative-Ring f)

  linear-transform-left-module-Commutative-Ring : UU (l1 ⊔ l2)
  linear-transform-left-module-Commutative-Ring =
    type-subtype is-linear-transform-prop-left-module-Commutative-Ring

module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-transform-left-module-Commutative-Ring R M)
  where

  map-linear-transform-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring R M →
    type-left-module-Commutative-Ring R M
  map-linear-transform-left-module-Commutative-Ring = pr1 f

  is-linear-transform-map-linear-transform-left-module-Commutative-Ring :
    is-linear-transform-left-module-Commutative-Ring R M
      ( map-linear-transform-left-module-Commutative-Ring)
  is-linear-transform-map-linear-transform-left-module-Commutative-Ring = pr2 f
```

## Properties

### A linear transformation maps zero to zero

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-transform-left-module-Commutative-Ring R M)
  where

  abstract
    is-zero-map-zero-linear-transform-left-module-Commutative-Ring :
      is-zero-left-module-Commutative-Ring R M
        ( map-linear-transform-left-module-Commutative-Ring R M f
          ( zero-left-module-Commutative-Ring R M))
    is-zero-map-zero-linear-transform-left-module-Commutative-Ring =
      is-zero-map-zero-linear-map-left-module-Commutative-Ring R M M f
```

### A linear map maps `-v` to the negation of the map of `v`

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-transform-left-module-Commutative-Ring R M)
  where

  abstract
    map-neg-linear-transform-left-module-Commutative-Ring :
      (v : type-left-module-Commutative-Ring R M) →
      map-linear-transform-left-module-Commutative-Ring R M f
        ( neg-left-module-Commutative-Ring R M v) ＝
      neg-left-module-Commutative-Ring R M
        ( map-linear-transform-left-module-Commutative-Ring R M f v)
    map-neg-linear-transform-left-module-Commutative-Ring =
      map-neg-linear-map-left-module-Commutative-Ring R M M f
```

### The identity map is a linear transformation

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  is-linear-id-left-module-Commutative-Ring :
    is-linear-transform-left-module-Commutative-Ring R M id
  is-linear-id-left-module-Commutative-Ring =
    is-linear-id-left-module-Ring (ring-Commutative-Ring R) M

  id-linear-transform-left-module-Commutative-Ring :
    linear-transform-left-module-Commutative-Ring R M
  id-linear-transform-left-module-Commutative-Ring =
    id-linear-transform-left-module-Ring (ring-Commutative-Ring R) M
```

### The composition of linear transformations is a linear transformation

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (g :
    type-left-module-Commutative-Ring R M →
    type-left-module-Commutative-Ring R M)
  (f :
    type-left-module-Commutative-Ring R M →
    type-left-module-Commutative-Ring R M)
  where

  abstract
    is-linear-transform-comp-is-linear-transform-left-module-Commutative-Ring :
      is-linear-transform-left-module-Commutative-Ring R M g →
      is-linear-transform-left-module-Commutative-Ring R M f →
      is-linear-transform-left-module-Commutative-Ring R M (g ∘ f)
    is-linear-transform-comp-is-linear-transform-left-module-Commutative-Ring =
      is-linear-comp-is-linear-map-left-module-Commutative-Ring R M M M g f
```

### The linear composition of linear transformations

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (g : linear-transform-left-module-Commutative-Ring R M)
  (f : linear-transform-left-module-Commutative-Ring R M)
  where

  comp-linear-transform-left-module-Commutative-Ring :
    linear-transform-left-module-Commutative-Ring R M
  comp-linear-transform-left-module-Commutative-Ring =
    comp-linear-map-left-module-Commutative-Ring R M M M g f
```

### Iterating linear transformations

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  abstract
    is-linear-transform-iterate-map-linear-transform-left-module-Commutative-Ring :
      (n : ℕ) (f : linear-transform-left-module-Commutative-Ring R M) →
      is-linear-transform-left-module-Commutative-Ring R M
        ( iterate n (map-linear-transform-left-module-Commutative-Ring R M f))
    is-linear-transform-iterate-map-linear-transform-left-module-Commutative-Ring =
      is-linear-transform-iterate-map-linear-transform-left-module-Ring
        ( ring-Commutative-Ring R)
        ( M)

  iterate-linear-transform-left-module-Commutative-Ring :
    ℕ → linear-transform-left-module-Commutative-Ring R M →
    linear-transform-left-module-Commutative-Ring R M
  iterate-linear-transform-left-module-Commutative-Ring =
    iterate-linear-transform-left-module-Ring (ring-Commutative-Ring R) M
```

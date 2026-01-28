# Linear endomorphisms on left modules over commutative rings

```agda
module linear-algebra.linear-endomorphisms-left-modules-commutative-rings where
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
open import linear-algebra.linear-endomorphisms-left-modules-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-rings
```

</details>

## Idea

A
{{#concept "linear endomorphism" Disambiguation="on left modules over commutative rings" Agda=linear-endo-left-module-Commutative-Ring}}
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

  is-linear-endo-prop-left-module-Commutative-Ring :
    ( type-left-module-Commutative-Ring R M →
      type-left-module-Commutative-Ring R M) →
    Prop (l1 ⊔ l2)
  is-linear-endo-prop-left-module-Commutative-Ring =
    is-linear-map-prop-left-module-Commutative-Ring R M M

  is-linear-endo-left-module-Commutative-Ring :
    ( type-left-module-Commutative-Ring R M →
      type-left-module-Commutative-Ring R M) →
    UU (l1 ⊔ l2)
  is-linear-endo-left-module-Commutative-Ring f =
    type-Prop (is-linear-endo-prop-left-module-Commutative-Ring f)

  linear-endo-left-module-Commutative-Ring : UU (l1 ⊔ l2)
  linear-endo-left-module-Commutative-Ring =
    type-subtype is-linear-endo-prop-left-module-Commutative-Ring

module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  where

  map-linear-endo-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring R M →
    type-left-module-Commutative-Ring R M
  map-linear-endo-left-module-Commutative-Ring = pr1 f

  is-linear-endo-map-linear-endo-left-module-Commutative-Ring :
    is-linear-endo-left-module-Commutative-Ring R M
      ( map-linear-endo-left-module-Commutative-Ring)
  is-linear-endo-map-linear-endo-left-module-Commutative-Ring = pr2 f
```

## Properties

### A linear transformation maps zero to zero

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  where

  abstract
    is-zero-map-zero-linear-endo-left-module-Commutative-Ring :
      is-zero-left-module-Commutative-Ring R M
        ( map-linear-endo-left-module-Commutative-Ring R M f
          ( zero-left-module-Commutative-Ring R M))
    is-zero-map-zero-linear-endo-left-module-Commutative-Ring =
      is-zero-map-zero-linear-map-left-module-Commutative-Ring R M M f
```

### A linear map maps `-v` to the negation of the map of `v`

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (f : linear-endo-left-module-Commutative-Ring R M)
  where

  abstract
    map-neg-linear-endo-left-module-Commutative-Ring :
      (v : type-left-module-Commutative-Ring R M) →
      map-linear-endo-left-module-Commutative-Ring R M f
        ( neg-left-module-Commutative-Ring R M v) ＝
      neg-left-module-Commutative-Ring R M
        ( map-linear-endo-left-module-Commutative-Ring R M f v)
    map-neg-linear-endo-left-module-Commutative-Ring =
      map-neg-linear-map-left-module-Commutative-Ring R M M f
```

### The identity map is a linear transformation

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  is-linear-map-id-left-module-Commutative-Ring :
    is-linear-endo-left-module-Commutative-Ring R M id
  is-linear-map-id-left-module-Commutative-Ring =
    is-linear-map-id-left-module-Ring (ring-Commutative-Ring R) M

  id-linear-endo-left-module-Commutative-Ring :
    linear-endo-left-module-Commutative-Ring R M
  id-linear-endo-left-module-Commutative-Ring =
    id-linear-endo-left-module-Ring (ring-Commutative-Ring R) M
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
    is-linear-endo-comp-left-module-Commutative-Ring :
      is-linear-endo-left-module-Commutative-Ring R M g →
      is-linear-endo-left-module-Commutative-Ring R M f →
      is-linear-endo-left-module-Commutative-Ring R M (g ∘ f)
    is-linear-endo-comp-left-module-Commutative-Ring =
      is-linear-map-comp-left-module-Commutative-Ring R M M M g f
```

### The linear composition of linear transformations

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (g : linear-endo-left-module-Commutative-Ring R M)
  (f : linear-endo-left-module-Commutative-Ring R M)
  where

  comp-linear-endo-left-module-Commutative-Ring :
    linear-endo-left-module-Commutative-Ring R M
  comp-linear-endo-left-module-Commutative-Ring =
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
    is-linear-endo-iterate-map-left-module-Commutative-Ring :
      (n : ℕ) (f : linear-endo-left-module-Commutative-Ring R M) →
      is-linear-endo-left-module-Commutative-Ring R M
        ( iterate n (map-linear-endo-left-module-Commutative-Ring R M f))
    is-linear-endo-iterate-map-left-module-Commutative-Ring =
      is-linear-endo-iterate-map-linear-endo-left-module-Ring
        ( ring-Commutative-Ring R)
        ( M)

  iterate-linear-endo-left-module-Commutative-Ring :
    ℕ → linear-endo-left-module-Commutative-Ring R M →
    linear-endo-left-module-Commutative-Ring R M
  iterate-linear-endo-left-module-Commutative-Ring =
    iterate-linear-endo-left-module-Ring (ring-Commutative-Ring R) M
```

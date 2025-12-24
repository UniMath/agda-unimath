# Linear transformations on left modules of rings

```agda
module linear-algebra.linear-transformations-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "linear transformation" Disambiguation="of a left module of a ring" Agda=linear-transform-left-module-Ring}}
of a [left module](linear-algebra.left-modules-rings.md) `M` over a
[ring](ring-theory.rings.md) is a
[linear map](linear-algebra.linear-maps-left-modules-rings.md) from `M` to
itself.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  is-linear-transform-prop-left-module-Ring :
    (type-left-module-Ring R M → type-left-module-Ring R M) → Prop (l1 ⊔ l2)
  is-linear-transform-prop-left-module-Ring =
    is-linear-map-prop-left-module-Ring R M M

  is-linear-transform-left-module-Ring :
    (type-left-module-Ring R M → type-left-module-Ring R M) → UU (l1 ⊔ l2)
  is-linear-transform-left-module-Ring = is-linear-map-left-module-Ring R M M

  linear-transform-left-module-Ring : UU (l1 ⊔ l2)
  linear-transform-left-module-Ring = linear-map-left-module-Ring R M M

module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (f : linear-transform-left-module-Ring R M)
  where

  map-linear-transform-left-module-Ring :
    type-left-module-Ring R M → type-left-module-Ring R M
  map-linear-transform-left-module-Ring = pr1 f

  is-linear-map-linear-transform-left-module-Ring :
    is-linear-transform-left-module-Ring R M
      ( map-linear-transform-left-module-Ring)
  is-linear-map-linear-transform-left-module-Ring = pr2 f
```

## Properties

### A linear transformation maps zero to zero

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (f : linear-transform-left-module-Ring R M)
  where

  abstract
    is-zero-map-zero-linear-transform-left-module-Ring :
      is-zero-left-module-Ring R M
        ( map-linear-transform-left-module-Ring R M f
          ( zero-left-module-Ring R M))
    is-zero-map-zero-linear-transform-left-module-Ring =
      is-zero-map-zero-linear-map-left-module-Ring R M M f
```

### A linear transformation maps `-x` to the negation of the map of `x`

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (f : linear-transform-left-module-Ring R M)
  where

  abstract
    map-neg-linear-transform-left-module-Ring :
      (x : type-left-module-Ring R M) →
      map-linear-transform-left-module-Ring R M f
        ( neg-left-module-Ring R M x) ＝
      neg-left-module-Ring R M (map-linear-transform-left-module-Ring R M f x)
    map-neg-linear-transform-left-module-Ring =
      map-neg-linear-map-left-module-Ring R M M f
```

### The identity map is a linear transformation

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  is-linear-id-left-module-Ring : is-linear-map-left-module-Ring R M M id
  is-linear-id-left-module-Ring = (λ _ _ → refl) , (λ _ _ → refl)

  id-linear-transform-left-module-Ring : linear-transform-left-module-Ring R M
  id-linear-transform-left-module-Ring = (id , is-linear-id-left-module-Ring)
```

### The composition of linear transformations is a linear transformation

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (g : type-left-module-Ring R M → type-left-module-Ring R M)
  (f : type-left-module-Ring R M → type-left-module-Ring R M)
  where

  abstract
    is-linear-transform-comp-is-linear-transform-left-module-Ring :
      is-linear-transform-left-module-Ring R M g →
      is-linear-transform-left-module-Ring R M f →
      is-linear-transform-left-module-Ring R M (g ∘ f)
    is-linear-transform-comp-is-linear-transform-left-module-Ring =
      is-linear-comp-is-linear-map-left-module-Ring R M M M g f
```

### The linear composition of linear transformations

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (g : linear-transform-left-module-Ring R M)
  (f : linear-transform-left-module-Ring R M)
  where

  comp-linear-transform-left-module-Ring : linear-transform-left-module-Ring R M
  comp-linear-transform-left-module-Ring =
    comp-linear-map-left-module-Ring R M M M g f
```

### Iterating linear transformations

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (V : left-module-Ring l2 R)
  where

  abstract
    is-linear-transform-iterate-map-linear-transform-left-module-Ring :
      (n : ℕ) (f : linear-transform-left-module-Ring R V) →
      is-linear-transform-left-module-Ring R V
        ( iterate n (map-linear-transform-left-module-Ring R V f))
    is-linear-transform-iterate-map-linear-transform-left-module-Ring 0 _ =
      is-linear-id-left-module-Ring R V
    is-linear-transform-iterate-map-linear-transform-left-module-Ring
      (succ-ℕ n) f =
      is-linear-transform-comp-is-linear-transform-left-module-Ring
        ( R)
        ( V)
        ( map-linear-transform-left-module-Ring R V f)
        ( iterate n (map-linear-transform-left-module-Ring R V f))
        ( is-linear-map-linear-transform-left-module-Ring R V f)
        ( is-linear-transform-iterate-map-linear-transform-left-module-Ring n f)

  iterate-linear-transform-left-module-Ring :
    ℕ → linear-transform-left-module-Ring R V →
    linear-transform-left-module-Ring R V
  iterate-linear-transform-left-module-Ring n f =
    ( iterate n (map-linear-transform-left-module-Ring R V f) ,
      is-linear-transform-iterate-map-linear-transform-left-module-Ring n f)
```

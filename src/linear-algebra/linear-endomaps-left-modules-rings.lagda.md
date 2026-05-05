# Linear endomaps on left modules of rings

```agda
module linear-algebra.linear-endomaps-left-modules-rings where
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
{{#concept "linear endomap" Disambiguation="of a left module of a ring" Agda=linear-endo-left-module-Ring}}
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

  is-linear-endo-prop-left-module-Ring :
    (type-left-module-Ring R M → type-left-module-Ring R M) → Prop (l1 ⊔ l2)
  is-linear-endo-prop-left-module-Ring =
    is-linear-map-prop-left-module-Ring R M M

  is-linear-endo-left-module-Ring :
    (type-left-module-Ring R M → type-left-module-Ring R M) → UU (l1 ⊔ l2)
  is-linear-endo-left-module-Ring = is-linear-map-left-module-Ring R M M

  linear-endo-left-module-Ring : UU (l1 ⊔ l2)
  linear-endo-left-module-Ring = linear-map-left-module-Ring R M M

module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (f : linear-endo-left-module-Ring R M)
  where

  map-linear-endo-left-module-Ring :
    type-left-module-Ring R M → type-left-module-Ring R M
  map-linear-endo-left-module-Ring = pr1 f

  is-linear-map-linear-endo-left-module-Ring :
    is-linear-endo-left-module-Ring R M
      ( map-linear-endo-left-module-Ring)
  is-linear-map-linear-endo-left-module-Ring = pr2 f
```

## Properties

### A linear endomap maps zero to zero

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (f : linear-endo-left-module-Ring R M)
  where

  abstract
    is-zero-map-zero-linear-endo-left-module-Ring :
      is-zero-left-module-Ring R M
        ( map-linear-endo-left-module-Ring R M f
          ( zero-left-module-Ring R M))
    is-zero-map-zero-linear-endo-left-module-Ring =
      is-zero-map-zero-linear-map-left-module-Ring R M M f
```

### A linear endomap maps `-x` to the negation of the map of `x`

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (f : linear-endo-left-module-Ring R M)
  where

  abstract
    map-neg-linear-endo-left-module-Ring :
      (x : type-left-module-Ring R M) →
      map-linear-endo-left-module-Ring R M f
        ( neg-left-module-Ring R M x) ＝
      neg-left-module-Ring R M (map-linear-endo-left-module-Ring R M f x)
    map-neg-linear-endo-left-module-Ring =
      map-neg-linear-map-left-module-Ring R M M f
```

### The identity map is a linear endomap

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  is-linear-map-id-left-module-Ring : is-linear-map-left-module-Ring R M M id
  is-linear-map-id-left-module-Ring = (λ _ _ → refl) , (λ _ _ → refl)

  id-linear-endo-left-module-Ring : linear-endo-left-module-Ring R M
  id-linear-endo-left-module-Ring = (id , is-linear-map-id-left-module-Ring)
```

### Composition of linear endomaps

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (g : type-left-module-Ring R M → type-left-module-Ring R M)
  (f : type-left-module-Ring R M → type-left-module-Ring R M)
  where

  abstract
    is-linear-endo-comp-left-module-Ring :
      is-linear-endo-left-module-Ring R M g →
      is-linear-endo-left-module-Ring R M f →
      is-linear-endo-left-module-Ring R M (g ∘ f)
    is-linear-endo-comp-left-module-Ring =
      is-linear-map-comp-left-module-Ring R M M M g f
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (g : linear-endo-left-module-Ring R M)
  (f : linear-endo-left-module-Ring R M)
  where

  comp-linear-endo-left-module-Ring : linear-endo-left-module-Ring R M
  comp-linear-endo-left-module-Ring =
    comp-linear-map-left-module-Ring R M M M g f
```

### Iterating linear endomaps

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (V : left-module-Ring l2 R)
  where

  abstract
    is-linear-endo-iterate-map-linear-endo-left-module-Ring :
      (n : ℕ) (f : linear-endo-left-module-Ring R V) →
      is-linear-endo-left-module-Ring R V
        ( iterate n (map-linear-endo-left-module-Ring R V f))
    is-linear-endo-iterate-map-linear-endo-left-module-Ring 0 _ =
      is-linear-map-id-left-module-Ring R V
    is-linear-endo-iterate-map-linear-endo-left-module-Ring
      (succ-ℕ n) f =
      is-linear-endo-comp-left-module-Ring
        ( R)
        ( V)
        ( map-linear-endo-left-module-Ring R V f)
        ( iterate n (map-linear-endo-left-module-Ring R V f))
        ( is-linear-map-linear-endo-left-module-Ring R V f)
        ( is-linear-endo-iterate-map-linear-endo-left-module-Ring n f)

  iterate-linear-endo-left-module-Ring :
    ℕ → linear-endo-left-module-Ring R V →
    linear-endo-left-module-Ring R V
  iterate-linear-endo-left-module-Ring n f =
    ( iterate n (map-linear-endo-left-module-Ring R V f) ,
      is-linear-endo-iterate-map-linear-endo-left-module-Ring n f)
```

# Lax functors between large noncoherent wild (∞,∞)-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.lax-functors-noncoherent-large-wild-infinity-infinity-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.maps-globular-types

open import wild-category-theory.lax-functors-noncoherent-wild-infinity-infinity-precategories
open import wild-category-theory.maps-noncoherent-large-wild-infinity-infinity-precategories
open import wild-category-theory.maps-noncoherent-wild-infinity-infinity-precategories
open import wild-category-theory.noncoherent-large-wild-infinity-infinity-precategories
open import wild-category-theory.noncoherent-wild-infinity-infinity-precategories
```

</details>

## Idea

A
{{#concept "lax-functor" Disambiguation="between noncoherent large wild $(∞,∞)$-precategories" Agda=lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory}}
`f` between
[noncoherent wild $(∞,∞)$-precategories](wild-category-theory.noncoherent-large-wild-infinity-infinity-precategories.md)
`𝒜` and `ℬ` is a
[map of noncoherent wild $(∞,∞)$-precategories](wild-category-theory.maps-noncoherent-large-wild-infinity-infinity-precategories.md)
such that... 🥁🥁🥁

## Definitions

### The predicate of being a functor between noncoherent wild $(∞,∞)$-precategories

```agda
record
  is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  {δ : Level → Level}
  {𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α1 β1}
  {ℬ : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α2 β2}
  (F : map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ 𝒜 ℬ) : UUω
  where
  field
    preserves-id-hom-is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      {l : Level}
      (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l) →
      2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F
          ( id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 {x = x}))
        ( id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
          { x = obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F x})

    preserves-comp-hom-is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      {l1 l2 l3 : Level}
      {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
      {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2}
      {z : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l3}
      (g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 y z)
      (f : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y) →
      2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F
          ( comp-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 g f))
        ( comp-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
          ( hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F g)
          ( hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F f))

    is-functor-map-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      {l1 l2 : Level}
      (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1)
      (y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2) →
      is-lax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( F)
          ( x)
          ( y))

open is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory public
```

### The type of lax functors between noncoherent wild $(∞,∞)$-precategories

```agda
record
  lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  (δ : Level → Level)
  (𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α2 β2) : UUω
  where

  field
    map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ 𝒜 ℬ

    is-functor-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
```

```agda
  obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l : Level} →
    obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l →
    obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ (δ l)
  obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2} →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
      ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y)
  hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory

  preserves-id-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l : Level}
    (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l) →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 {x = x}))
      ( id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        { x = obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x})
  preserves-id-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    preserves-id-hom-is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( is-functor-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  preserves-comp-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2}
    {z : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l3}
    (g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( comp-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory g)
        ( hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f))
  preserves-comp-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    preserves-comp-hom-is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( is-functor-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  2-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2}
    {f g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 f g →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f)
      ( hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory g)
  2-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    2-hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory

  hom-globular-type-map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2} →
    map-Globular-Type
      ( hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y))
  hom-globular-type-map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    hom-globular-type-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1)
    (y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2) →
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( ℬ)
        ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y))
  map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  hom-noncoherent-wild-⟨∞,∞⟩-precategory-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1)
    (y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2) →
    lax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( ℬ)
        ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y))
  hom-noncoherent-wild-⟨∞,∞⟩-precategory-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
    x y =
    ( map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( x)
        ( y) ,
      is-functor-map-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( is-functor-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))

open lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory public
```

### The identity lax functor on a noncoherent large wild $(∞,∞)$-precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α β)
  where

  is-functor-id-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( id-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜)
  is-functor-id-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
      .preserves-id-hom-is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        x →
        id-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜
      .preserves-comp-hom-is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        g f →
        id-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜
      .is-functor-map-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y →
        is-functor-id-lax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
          ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
            ( 𝒜)
            ( x)
            ( y))

  id-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory (λ l → l) 𝒜 𝒜
  id-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory →
      id-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜
    .is-functor-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory →
      is-functor-id-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
```

### Composition of lax functors between noncoherent wild $(∞,∞)$-precategories

```agda
module _
  {α1 α2 α3 : Level → Level}
  {β1 β2 β3 : Level → Level → Level}
  {δ1 δ2 : Level → Level}
  {𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α1 β1}
  {ℬ : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α2 β2}
  {𝒞 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α3 β3}
  (G : lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ2 ℬ 𝒞)
  (F : lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ1 𝒜 ℬ)
  where

  map-comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory (λ l → δ2 (δ1 l)) 𝒜 𝒞
  map-comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    comp-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory G)
      ( map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F)

  is-functor-comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
  is-functor-comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .preserves-id-hom-is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      x →
      comp-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒞
        ( preserves-id-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( G)
          ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F x))
        ( 2-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory G
          ( preserves-id-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
            ( F)
            ( x)))
    .preserves-comp-hom-is-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      g f →
      comp-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒞
        ( preserves-comp-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( G)
          ( hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F g)
          ( hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F f))
        ( 2-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory G
          ( preserves-comp-hom-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
            ( F)
            ( g)
            ( f)))
    .is-functor-map-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y →
      is-functor-comp-lax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( G)
          ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F x)
          ( obj-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F y))
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( F)
          ( x)
          ( y))

  comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory (λ l → δ2 (δ1 l)) 𝒜 𝒞
  comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .map-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory →
      map-comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
    .is-functor-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory →
      is-functor-comp-lax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
```

# Functors between noncoherent wild (∞,∞)-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.functors-noncoherent-wild-infinity-infinity-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.maps-globular-types

open import wild-category-theory.maps-noncoherent-wild-infinity-infinity-precategories
open import wild-category-theory.noncoherent-wild-infinity-infinity-precategories
```

</details>

## Idea

A
{{#concept "functor" Disambiguation="between noncoherent wild $(∞,∞)$-precategories" Agda=functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory}}
`f` between
[noncoherent wild $(∞,∞)$-precategories](wild-category-theory.noncoherent-wild-infinity-infinity-precategories.md)
`𝒜` and `ℬ` is a
[map of noncoherent wild $(∞,∞)$-precategories](wild-category-theory.maps-noncoherent-wild-infinity-infinity-precategories.md)
such that... 🥁🥁🥁

## Definitions

### The predicate of being a functor between noncoherent wild $(∞,∞)$-precategories

```agda
record
  is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  (F : map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ) : UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive
  field
    preserves-id-hom-is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
      (x : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
      2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F
          ( id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 {x}))
        ( id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
          { obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x})

    preserves-comp-hom-is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
      {x y z : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜}
      (g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 y z)
      (f : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y) →
      2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F
          ( comp-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 g f))
        ( comp-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
          ( hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F g)
          ( hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F f))

    is-functor-map-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
      (x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
      is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
          ( F)
          ( x)
          ( y))

open is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory public
```

### The type of functors between noncoherent wild $(∞,∞)$-precategories

```agda
functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ =
  Σ ( map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
    ( is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

module _
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  (F : functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
  where

  map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ
  map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory = pr1 F

  is-functor-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
  is-functor-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory = pr2 F

  obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 →
    obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
  obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜} →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
      ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory y)
  hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory

  preserves-id-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 {x}))
      ( id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        { obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x})
  preserves-id-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    preserves-id-hom-is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( is-functor-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  preserves-comp-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y z : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜}
    (g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( comp-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory g)
        ( hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory f))
  preserves-comp-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    preserves-comp-hom-is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( is-functor-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  2-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜}
    {f g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 f g →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory f)
      ( hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory g)
  2-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    2-hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory

  hom-globular-type-map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜} →
    map-Globular-Type
      ( hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory y))
  hom-globular-type-map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( ℬ)
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory y))
  map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  hom-noncoherent-wild-⟨∞,∞⟩-precategory-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
    functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( ℬ)
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory y))
  hom-noncoherent-wild-⟨∞,∞⟩-precategory-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    x y =
    ( map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( x)
        ( y) ,
      is-functor-map-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( is-functor-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))
```

### The identity functor on a noncoherent wild $(∞,∞)$-precategory

```agda
is-functor-id-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2) →
  is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    ( id-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜)
is-functor-id-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 =
  λ where
    .preserves-id-hom-is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x →
      id-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜
    .preserves-comp-hom-is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory g f →
      id-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜
    .is-functor-map-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y →
      is-functor-id-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
          ( 𝒜)
          ( x)
          ( y))

id-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2) →
  functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 𝒜
id-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 =
  ( id-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ,
    is-functor-id-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜)
```

### Composition of functors between noncoherent wild $(∞,∞)$-precategories

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l5 l6}
  (G : functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ 𝒞)
  (F : functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
  where

  map-comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 𝒞
  map-comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    comp-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G)
      ( map-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F)

is-functor-comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l5 l6}
  (G : functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ 𝒞)
  (F : functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ) →
  is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    ( map-comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G F)
is-functor-comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory {𝒞 = 𝒞} G F =
  λ where
  .preserves-id-hom-is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x →
    comp-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒞
      ( preserves-id-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x))
      ( 2-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G
        ( preserves-id-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x))
  .preserves-comp-hom-is-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory g f →
    comp-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒞
      ( preserves-comp-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G
        ( hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F g)
        ( hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F f))
      ( 2-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G
        ( preserves-comp-hom-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F
          ( g)
          ( f)))
  .is-functor-map-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y →
    is-functor-comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( G)
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x)
        ( obj-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( F)
        ( x)
        ( y))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l5 l6}
  (G : functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ 𝒞)
  (F : functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
  where

  comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 𝒞
  pr1 comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    map-comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G F
  pr2 comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    is-functor-comp-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G F
```

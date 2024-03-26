# Colax functors between large noncoherent wild (∞,∞)-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.colax-functors-noncoherent-large-wild-infinity-infinity-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.maps-globular-types

open import wild-category-theory.colax-functors-noncoherent-wild-infinity-infinity-precategories
open import wild-category-theory.maps-noncoherent-large-wild-infinity-infinity-precategories
open import wild-category-theory.maps-noncoherent-wild-infinity-infinity-precategories
open import wild-category-theory.noncoherent-large-wild-infinity-infinity-precategories
open import wild-category-theory.noncoherent-wild-infinity-infinity-precategories
```

</details>

## Idea

A
{{#concept "colax functor" Disambiguation="between noncoherent large wild $(∞,∞)$-precategories" Agda=colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory}}
`f` between
[noncoherent large wild $(∞,∞)$-precategories](wild-category-theory.noncoherent-large-wild-infinity-infinity-precategories.md)
`𝒜` and `ℬ` is a
[map of noncoherent large wild $(∞,∞)$-precategories](wild-category-theory.maps-noncoherent-large-wild-infinity-infinity-precategories.md)
that preserves identity morphisms and composition _colaxly_. This means that for
every $n$-morphism `f` in `𝒜`, where we take $0$-morphisms to be objects, there
is an $(n+2)$-morphism

```text
  Fₙ₊₁ (id-hom 𝒜 f) ⇒ id-hom ℬ (Fₙ f)
```

in `ℬ`,

and for every pair of composable $n$-morphisms `g` after `f` in `𝒜`, there is an
$(n+1)$-morphism

```text
  Fₙ (g ∘ f) ⇒ (Fₙ g) ∘ (Fₙ f)
```

in `ℬ`.

## Definitions

### The predicate of being a functor between noncoherent wild $(∞,∞)$-precategories

```agda
record
  is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  {δ : Level → Level}
  {𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α1 β1}
  {ℬ : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α2 β2}
  (F : map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ 𝒜 ℬ) : UUω
  where
  field
    preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      {l : Level}
      (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l) →
      2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F
          ( id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 {x = x}))
        ( id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
          { x = obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F x})

    preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
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
      is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( F)
          ( x)
          ( y))

open is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory public
```

### The type of colax functors between noncoherent wild $(∞,∞)$-precategories

```agda
record
  colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  (δ : Level → Level)
  (𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α2 β2) : UUω
  where

  field
    map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ 𝒜 ℬ

    is-functor-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
```

```agda
  obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l : Level} →
    obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l →
    obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ (δ l)
  obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    obj-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2} →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
      ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y)
  hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory

  preserves-id-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l : Level}
    (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l) →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 {x = x}))
      ( id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        { x = obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x})
  preserves-id-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( is-functor-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2}
    {z : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l3}
    (g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( comp-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory g)
        ( hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f))
  preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( is-functor-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  2-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2}
    {f g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 f g →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f)
      ( hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory g)
  2-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    2-hom-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory

  hom-globular-type-map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2} →
    map-Globular-Type
      ( hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory ℬ
        ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y))
  hom-globular-type-map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    hom-globular-type-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
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
        ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y))
  map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l1)
    (y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜 l2) →
    colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y))
  hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
    x y =
    ( map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( x)
        ( y) ,
      is-functor-map-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        ( is-functor-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))

open colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory public
```

### The identity colax functor on a noncoherent large wild $(∞,∞)$-precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α β)
  where

  is-functor-id-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( id-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜)
  is-functor-id-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
      .preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        x →
        id-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜
      .preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
        g f →
        id-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜
      .is-functor-map-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y →
        is-functor-id-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
          ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
            ( 𝒜)
            ( x)
            ( y))

  id-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory (λ l → l) 𝒜 𝒜
  id-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory →
      id-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒜
    .is-functor-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory →
      is-functor-id-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
```

### Composition of colax functors between noncoherent wild $(∞,∞)$-precategories

```agda
module _
  {α1 α2 α3 : Level → Level}
  {β1 β2 β3 : Level → Level → Level}
  {δ1 δ2 : Level → Level}
  {𝒜 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α1 β1}
  {ℬ : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α2 β2}
  {𝒞 : Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory α3 β3}
  (G : colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ2 ℬ 𝒞)
  (F : colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory δ1 𝒜 ℬ)
  where

  map-comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory (λ l → δ2 (δ1 l)) 𝒜 𝒞
  map-comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    comp-map-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory G)
      ( map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F)

  is-functor-comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      ( map-comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
  is-functor-comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      x →
      comp-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒞
        ( preserves-id-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( G)
          ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F x))
        ( 2-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory G
          ( preserves-id-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
            ( F)
            ( x)))
    .preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
      g f →
      comp-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory 𝒞
        ( preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( G)
          ( hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F g)
          ( hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F f))
        ( 2-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory G
          ( preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
            ( F)
            ( g)
            ( f)))
    .is-functor-map-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y →
      is-functor-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( G)
          ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F x)
          ( obj-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory F y))
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
          ( F)
          ( x)
          ( y))

  comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory (λ l → δ2 (δ1 l)) 𝒜 𝒞
  comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .map-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory →
      map-comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
    .is-functor-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory →
      is-functor-comp-colax-functor-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
```

# Colax functors between large noncoherent wild higher precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.colax-functors-noncoherent-large-wild-higher-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.maps-globular-types

open import wild-category-theory.colax-functors-noncoherent-wild-higher-precategories
open import wild-category-theory.maps-noncoherent-large-wild-higher-precategories
open import wild-category-theory.maps-noncoherent-wild-higher-precategories
open import wild-category-theory.noncoherent-large-wild-higher-precategories
open import wild-category-theory.noncoherent-wild-higher-precategories
```

</details>

## Idea

A
{{#concept "colax functor" Disambiguation="between noncoherent large wild higher precategories" Agda=colax-functor-Noncoherent-Large-Wild-Higher-Precategory}}
`f` between
[noncoherent large wild higher precategories](wild-category-theory.noncoherent-large-wild-higher-precategories.md)
`𝒜` and `ℬ` is a
[map of noncoherent large wild higher precategories](wild-category-theory.maps-noncoherent-large-wild-higher-precategories.md)
that preserves identity morphisms and composition _colaxly_. This means that for
every $n$-morphism `f` in `𝒜`, where we take $0$-morphisms to be objects, there
is an $(n+1)$-morphism

```text
  Fₙ₊₁ (id-hom 𝒜 f) ⇒ id-hom ℬ (Fₙ f)
```

in `ℬ`,

and for every pair of composable $(n+1)$-morphisms `g` after `f` in `𝒜`, there
is an $(n+2)$-morphism

```text
  Fₙ₊₁ (g ∘ f) ⇒ (Fₙ₊₁ g) ∘ (Fₙ₊₁ f)
```

in `ℬ`.

## Definitions

### The predicate of being a colax functor between noncoherent wild higher precategories

```agda
record
  is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  {δ : Level → Level}
  {𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1}
  {ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2}
  (F : map-Noncoherent-Large-Wild-Higher-Precategory δ 𝒜 ℬ) : UUω
  where
  field
    preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
      {l : Level}
      (x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l) →
      2-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
        ( hom-map-Noncoherent-Large-Wild-Higher-Precategory F
          ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 {x = x}))
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
          { x = obj-map-Noncoherent-Large-Wild-Higher-Precategory F x})

    preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
      {l1 l2 l3 : Level}
      {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
      {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2}
      {z : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l3}
      (g : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 y z)
      (f : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y) →
      2-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
        ( hom-map-Noncoherent-Large-Wild-Higher-Precategory F
          ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 g f))
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
          ( hom-map-Noncoherent-Large-Wild-Higher-Precategory F g)
          ( hom-map-Noncoherent-Large-Wild-Higher-Precategory F f))

    is-colax-functor-map-hom-Noncoherent-Large-Wild-Higher-Precategory :
      {l1 l2 : Level}
      (x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1)
      (y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2) →
      is-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( hom-noncoherent-wild-higher-precategory-map-Noncoherent-Large-Wild-Higher-Precategory
          ( F)
          ( x)
          ( y))

open is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory public
```

### The type of colax functors between noncoherent wild higher precategories

```agda
record
  colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  (δ : Level → Level)
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2) : UUω
  where

  field
    map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
      map-Noncoherent-Large-Wild-Higher-Precategory δ 𝒜 ℬ

    is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
      is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)
```

```agda
  obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l : Level} →
    obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l →
    obj-Noncoherent-Large-Wild-Higher-Precategory ℬ (δ l)
  obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    obj-map-Noncoherent-Large-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)

  hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y →
    hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
      ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory x)
      ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory y)
  hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    hom-map-Noncoherent-Large-Wild-Higher-Precategory
      map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l) →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 {x = x}))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
        { x = obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory x})
  preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      ( is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)

  preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2}
    {z : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l3}
    (g : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
        ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory g)
        ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory f))
  preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      ( is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)

  2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2}
    {f g : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 f g →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory f)
      ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory g)
  2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    2-hom-map-Noncoherent-Large-Wild-Higher-Precategory
      map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  hom-globular-type-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    map-Globular-Type
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory ℬ
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory y))
  hom-globular-type-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)

  map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2) →
    map-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory y))
  map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    hom-noncoherent-wild-higher-precategory-map-Noncoherent-Large-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)

  hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2) →
    colax-functor-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory y))
  hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    x y =
    ( map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        ( x)
        ( y) ,
      is-colax-functor-map-hom-Noncoherent-Large-Wild-Higher-Precategory
        ( is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)
        ( x)
        ( y))

open colax-functor-Noncoherent-Large-Wild-Higher-Precategory public
```

### The identity colax functor on a noncoherent large wild higher precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α β)
  where

  is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      ( id-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜)
  is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    λ where
      .preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        x →
        id-2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜
      .preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        g f →
        id-2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜
      .is-colax-functor-map-hom-Noncoherent-Large-Wild-Higher-Precategory x y →
        is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategory
          ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
            ( 𝒜)
            ( x)
            ( y))

  id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    colax-functor-Noncoherent-Large-Wild-Higher-Precategory (λ l → l) 𝒜 𝒜
  id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    λ where
    .map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory →
      id-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜
    .is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory →
      is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
```

### Composition of colax functors between noncoherent wild higher precategories

```agda
module _
  {α1 α2 α3 : Level → Level}
  {β1 β2 β3 : Level → Level → Level}
  {δ1 δ2 : Level → Level}
  {𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1}
  {ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2}
  {𝒞 : Noncoherent-Large-Wild-Higher-Precategory α3 β3}
  (G : colax-functor-Noncoherent-Large-Wild-Higher-Precategory δ2 ℬ 𝒞)
  (F : colax-functor-Noncoherent-Large-Wild-Higher-Precategory δ1 𝒜 ℬ)
  where

  map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    map-Noncoherent-Large-Wild-Higher-Precategory (λ l → δ2 (δ1 l)) 𝒜 𝒞
  map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    comp-map-Noncoherent-Large-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory G)
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory F)

  is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      ( map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)
  is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    λ where
    .preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      x →
      comp-2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
          ( G)
          ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory F x))
        ( 2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory G
          ( preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
            ( F)
            ( x)))
    .preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      g f →
      comp-2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
          ( G)
          ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory F g)
          ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory F f))
        ( 2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory G
          ( preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
            ( F)
            ( g)
            ( f)))
    .is-colax-functor-map-hom-Noncoherent-Large-Wild-Higher-Precategory x y →
      is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
          ( G)
          ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory F x)
          ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory F y))
        ( hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
          ( F)
          ( x)
          ( y))

  comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      ( λ l → δ2 (δ1 l))
      ( 𝒜)
      ( 𝒞)
  comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    λ where
    .map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory →
      map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    .is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory →
      is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
```

# Colax functors between noncoherent wild (∞,∞)-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.colax-functors-noncoherent-wild-infinity-infinity-precategories where
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
{{#concept "colax functor" Disambiguation="between noncoherent wild $(∞,∞)$-precategories" Agda=colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory}}
`F` between
[noncoherent wild $(∞,∞)$-precategories](wild-category-theory.noncoherent-wild-infinity-infinity-precategories.md)
`𝒜` and `ℬ` is a
[map of noncoherent wild $(∞,∞)$-precategories](wild-category-theory.maps-noncoherent-wild-infinity-infinity-precategories.md)
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

### The predicate of being a colax functor between noncoherent wild $(∞,∞)$-precategories

```agda
record
  is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  (F : map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ) : UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive
  field
    preserves-id-hom-is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
      (x : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
      2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F
          ( id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 {x}))
        ( id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
          { obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x})

    preserves-comp-hom-is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
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
      is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
          ( F)
          ( x)
          ( y))

open is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory public
```

### The type of colax functors between noncoherent wild $(∞,∞)$-precategories

```agda
colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ =
  Σ ( map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
    ( is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

module _
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  (F : colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
  where

  map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ
  map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory = pr1 F

  is-functor-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
  is-functor-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory = pr2 F

  obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 →
    obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
  obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    obj-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜} →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y →
    hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
      ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory y)
  hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory

  preserves-id-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 {x}))
      ( id-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        { obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x})
  preserves-id-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    preserves-id-hom-is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( is-functor-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  preserves-comp-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y z : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜}
    (g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( comp-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        ( hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory g)
        ( hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory f))
  preserves-comp-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    preserves-comp-hom-is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( is-functor-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  2-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜}
    {f g : hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 f g →
    2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory f)
      ( hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory g)
  2-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    2-hom-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory

  hom-globular-type-map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    {x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜} →
    map-Globular-Type
      ( hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory y))
  hom-globular-type-map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    hom-globular-type-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory y))
  map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    hom-noncoherent-wild-⟨∞,∞⟩-precategory-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)

  hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    (x y : obj-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜) →
    colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x)
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory y))
  hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    x y =
    ( map-hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( x)
        ( y) ,
      is-functor-map-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( is-functor-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))
```

### The identity colax functor on a noncoherent wild $(∞,∞)$-precategory

```agda
is-functor-id-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2) →
  is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    ( id-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜)
is-functor-id-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 =
  λ where
    .preserves-id-hom-is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      x →
      id-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜
    .preserves-comp-hom-is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      g f →
      id-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜
    .is-functor-map-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y →
      is-functor-id-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Wild-⟨∞,∞⟩-Precategory
          ( 𝒜)
          ( x)
          ( y))

id-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2) →
  colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 𝒜
id-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 =
  ( id-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ,
    is-functor-id-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜)
```

### Composition of colax functors between noncoherent wild $(∞,∞)$-precategories

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l5 l6}
  (G : colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
  where

  map-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    map-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 𝒞
  map-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    comp-map-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G)
      ( map-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F)

is-functor-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l5 l6}
  (G : colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ) →
  is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
    ( map-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G F)
is-functor-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory {𝒞 = 𝒞} G F =
  λ where
  .preserves-id-hom-is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory x →
    comp-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒞
      ( preserves-id-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x))
      ( 2-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G
        ( preserves-id-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F
          ( x)))
  .preserves-comp-hom-is-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory g f →
    comp-2-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒞
      ( preserves-comp-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G
        ( hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F g)
        ( hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F f))
      ( 2-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G
        ( preserves-comp-hom-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F
          ( g)
          ( f)))
  .is-functor-map-hom-Noncoherent-Wild-⟨∞,∞⟩-Precategory x y →
    is-functor-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( G)
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F x)
        ( obj-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory F y))
      ( hom-noncoherent-wild-⟨∞,∞⟩-precategory-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory
        ( F)
        ( x)
        ( y))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-⟨∞,∞⟩-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-⟨∞,∞⟩-Precategory l5 l6}
  (G : colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 ℬ)
  where

  comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory :
    colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory 𝒜 𝒞
  pr1 comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    map-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G F
  pr2 comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory =
    is-functor-comp-colax-functor-Noncoherent-Wild-⟨∞,∞⟩-Precategory G F
```

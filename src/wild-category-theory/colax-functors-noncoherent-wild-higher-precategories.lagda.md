# Colax functors between noncoherent wild higher precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.colax-functors-noncoherent-wild-higher-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.maps-globular-types

open import wild-category-theory.maps-noncoherent-wild-higher-precategories
open import wild-category-theory.noncoherent-wild-higher-precategories
```

</details>

## Idea

A
{{#concept "colax functor" Disambiguation="between noncoherent wild higher precategories" Agda=colax-functor-Noncoherent-Wild-Higher-Precategory}}
`F` between
[noncoherent wild higher precategories](wild-category-theory.noncoherent-wild-higher-precategories.md)
`𝒜` and `ℬ` is a
[map of noncoherent wild higher precategories](wild-category-theory.maps-noncoherent-wild-higher-precategories.md)
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
  is-colax-functor-Noncoherent-Wild-Higher-Precategory
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-Higher-Precategory l3 l4}
  (F : map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ) : UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive
  field
    preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
      (x : obj-Noncoherent-Wild-Higher-Precategory 𝒜) →
      2-hom-Noncoherent-Wild-Higher-Precategory ℬ
        ( hom-map-Noncoherent-Wild-Higher-Precategory F
          ( id-hom-Noncoherent-Wild-Higher-Precategory 𝒜 {x}))
        ( id-hom-Noncoherent-Wild-Higher-Precategory ℬ
          { obj-map-Noncoherent-Wild-Higher-Precategory F x})

    preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
      {x y z : obj-Noncoherent-Wild-Higher-Precategory 𝒜}
      (g : hom-Noncoherent-Wild-Higher-Precategory 𝒜 y z)
      (f : hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y) →
      2-hom-Noncoherent-Wild-Higher-Precategory ℬ
        ( hom-map-Noncoherent-Wild-Higher-Precategory F
          ( comp-hom-Noncoherent-Wild-Higher-Precategory 𝒜 g f))
        ( comp-hom-Noncoherent-Wild-Higher-Precategory ℬ
          ( hom-map-Noncoherent-Wild-Higher-Precategory F g)
          ( hom-map-Noncoherent-Wild-Higher-Precategory F f))

    is-colax-functor-map-hom-Noncoherent-Wild-Higher-Precategory :
      (x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜) →
      is-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( hom-noncoherent-wild-higher-precategory-map-Noncoherent-Wild-Higher-Precategory
          ( F)
          ( x)
          ( y))

open is-colax-functor-Noncoherent-Wild-Higher-Precategory public
```

### The type of colax functors between noncoherent wild higher precategories

```agda
colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ =
  Σ ( map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
    ( is-colax-functor-Noncoherent-Wild-Higher-Precategory)

module _
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-Higher-Precategory l3 l4}
  (F : colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  map-colax-functor-Noncoherent-Wild-Higher-Precategory :
    map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ
  map-colax-functor-Noncoherent-Wild-Higher-Precategory = pr1 F

  is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory :
    is-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory)
  is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory = pr2 F

  obj-colax-functor-Noncoherent-Wild-Higher-Precategory :
    obj-Noncoherent-Wild-Higher-Precategory 𝒜 →
    obj-Noncoherent-Wild-Higher-Precategory ℬ
  obj-colax-functor-Noncoherent-Wild-Higher-Precategory =
    obj-map-Noncoherent-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory)

  hom-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y →
    hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory x)
      ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory y)
  hom-colax-functor-Noncoherent-Wild-Higher-Precategory =
    hom-map-Noncoherent-Wild-Higher-Precategory
      map-colax-functor-Noncoherent-Wild-Higher-Precategory

  preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategory :
    (x : obj-Noncoherent-Wild-Higher-Precategory 𝒜) →
    2-hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( id-hom-Noncoherent-Wild-Higher-Precategory 𝒜 {x}))
      ( id-hom-Noncoherent-Wild-Higher-Precategory ℬ
        { obj-colax-functor-Noncoherent-Wild-Higher-Precategory x})
  preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategory =
    preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory)

  preserves-comp-hom-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y z : obj-Noncoherent-Wild-Higher-Precategory 𝒜}
    (g : hom-Noncoherent-Wild-Higher-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( comp-hom-Noncoherent-Wild-Higher-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Wild-Higher-Precategory ℬ
        ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory g)
        ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory f))
  preserves-comp-hom-colax-functor-Noncoherent-Wild-Higher-Precategory =
    preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory)

  2-hom-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜}
    {f g : hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Wild-Higher-Precategory 𝒜 f g →
    2-hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory f)
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory g)
  2-hom-colax-functor-Noncoherent-Wild-Higher-Precategory =
    2-hom-map-Noncoherent-Wild-Higher-Precategory
      map-colax-functor-Noncoherent-Wild-Higher-Precategory

  hom-globular-type-map-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    map-Globular-Type
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategory ℬ
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory y))
  hom-globular-type-map-colax-functor-Noncoherent-Wild-Higher-Precategory =
    hom-globular-type-map-Noncoherent-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory)

  map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategory :
    (x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜) →
    map-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory y))
  map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategory =
    hom-noncoherent-wild-higher-precategory-map-Noncoherent-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory)

  hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategory :
    (x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜) →
    colax-functor-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory y))
  hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategory
    x y =
    ( map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( x)
        ( y) ,
      is-colax-functor-map-hom-Noncoherent-Wild-Higher-Precategory
        ( is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory)
        ( x)
        ( y))
```

### The identity colax functor on a noncoherent wild higher precategory

```agda
is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2) →
  is-colax-functor-Noncoherent-Wild-Higher-Precategory
    ( id-map-Noncoherent-Wild-Higher-Precategory 𝒜)
is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 =
  λ where
    .preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory
      x →
      id-2-hom-Noncoherent-Wild-Higher-Precategory 𝒜
    .preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory
      g f →
      id-2-hom-Noncoherent-Wild-Higher-Precategory 𝒜
    .is-colax-functor-map-hom-Noncoherent-Wild-Higher-Precategory x y →
      is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
          ( 𝒜)
          ( x)
          ( y))

id-colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2) →
  colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 𝒜
id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 =
  ( id-map-Noncoherent-Wild-Higher-Precategory 𝒜 ,
    is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜)
```

### Composition of colax functors between noncoherent wild higher precategories

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-Higher-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-Higher-Precategory l5 l6}
  (G : colax-functor-Noncoherent-Wild-Higher-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory :
    map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒞
  map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    comp-map-Noncoherent-Wild-Higher-Precategory
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory G)
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory F)

is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-Higher-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-Higher-Precategory l5 l6}
  (G : colax-functor-Noncoherent-Wild-Higher-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ) →
  is-colax-functor-Noncoherent-Wild-Higher-Precategory
    ( map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory G F)
is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
  {𝒞 = 𝒞} G F =
  λ where
  .preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory x →
    comp-2-hom-Noncoherent-Wild-Higher-Precategory 𝒞
      ( preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategory G
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory F x))
      ( 2-hom-colax-functor-Noncoherent-Wild-Higher-Precategory G
        ( preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategory F
          ( x)))
  .preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory g f →
    comp-2-hom-Noncoherent-Wild-Higher-Precategory 𝒞
      ( preserves-comp-hom-colax-functor-Noncoherent-Wild-Higher-Precategory G
        ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory F g)
        ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory F f))
      ( 2-hom-colax-functor-Noncoherent-Wild-Higher-Precategory G
        ( preserves-comp-hom-colax-functor-Noncoherent-Wild-Higher-Precategory F
          ( g)
          ( f)))
  .is-colax-functor-map-hom-Noncoherent-Wild-Higher-Precategory x y →
    is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( G)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory F x)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory F y))
      ( hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategory
        ( F)
        ( x)
        ( y))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-Higher-Precategory l3 l4}
  {𝒞 : Noncoherent-Wild-Higher-Precategory l5 l6}
  (G : colax-functor-Noncoherent-Wild-Higher-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  comp-colax-functor-Noncoherent-Wild-Higher-Precategory :
    colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 𝒞
  pr1 comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory G F
  pr2 comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory G F
```

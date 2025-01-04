# Colax functors between large noncoherent ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.colax-functors-noncoherent-large-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-types
open import globular-types.large-colax-reflexive-globular-maps
open import globular-types.large-colax-transitive-globular-maps
open import globular-types.large-globular-maps

open import wild-category-theory.colax-functors-noncoherent-omega-precategories
open import wild-category-theory.maps-noncoherent-large-omega-precategories
open import wild-category-theory.maps-noncoherent-omega-precategories
open import wild-category-theory.noncoherent-large-omega-precategories
open import wild-category-theory.noncoherent-omega-precategories
```

</details>

## Idea

A
{{#concept "colax functor" Disambiguation="between noncoherent large ω-precategories" Agda=colax-functor-Noncoherent-Large-ω-Precategory}}
`f` between
[noncoherent large ω-precategories](wild-category-theory.noncoherent-large-omega-precategories.md)
`𝒜` and `ℬ` is a
[map of noncoherent large ω-precategories](wild-category-theory.maps-noncoherent-large-omega-precategories.md)
that preserves identity morphisms and composition _colaxly_. This means that for
every $n$-morphism `f` in `𝒜`, where we take $0$-morphisms to be objects, there
is an $(n+1)$-morphism

```text
  Fₙ₊₁ (id-hom 𝒜 f) ⇒ id-hom ℬ (Fₙ f)
```

in `ℬ`, and for every pair of composable $(n+1)$-morphisms `g` after `f` in `𝒜`,
there is an $(n+2)$-morphism

```text
  Fₙ₊₁ (g ∘ f) ⇒ (Fₙ₊₁ g) ∘ (Fₙ₊₁ f)
```

in `ℬ`.

## Definitions

### The predicate on maps between large noncoherent ω-precategories of preserving the identity structure

```agda
preserves-id-structure-map-Noncoherent-Large-ω-Precategory :
  {α1 α2 γ : Level → Level}
  {β1 β2 : Level → Level → Level}
  (𝒜 : Noncoherent-Large-ω-Precategory α1 β1)
  (ℬ : Noncoherent-Large-ω-Precategory α2 β2)
  (F : map-Noncoherent-Large-ω-Precategory γ 𝒜 ℬ) → UUω
preserves-id-structure-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ F =
  is-colax-reflexive-large-globular-map
    ( large-reflexive-globular-type-Noncoherent-Large-ω-Precategory
      𝒜)
    ( large-reflexive-globular-type-Noncoherent-Large-ω-Precategory
      ℬ)
    ( F)
```

### The predicate on maps between large noncoherent ω-precategories of preserving the composition structure

```agda
preserves-comp-structure-map-Noncoherent-Large-ω-Precategory :
  {α1 α2 γ : Level → Level}
  {β1 β2 : Level → Level → Level}
  (𝒜 : Noncoherent-Large-ω-Precategory α1 β1)
  (ℬ : Noncoherent-Large-ω-Precategory α2 β2)
  (F : map-Noncoherent-Large-ω-Precategory γ 𝒜 ℬ) → UUω
preserves-comp-structure-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ F =
  is-colax-transitive-large-globular-map
    ( large-transitive-globular-type-Noncoherent-Large-ω-Precategory
      𝒜)
    ( large-transitive-globular-type-Noncoherent-Large-ω-Precategory
      ℬ)
    ( F)
```

### The predicate of being a colax functor between noncoherent ω-precategories

```agda
record
  is-colax-functor-Noncoherent-Large-ω-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  {γ : Level → Level}
  (𝒜 : Noncoherent-Large-ω-Precategory α1 β1)
  (ℬ : Noncoherent-Large-ω-Precategory α2 β2)
  (F : map-Noncoherent-Large-ω-Precategory γ 𝒜 ℬ) : UUω
  where

  constructor
    make-is-colax-functor-Noncoherent-Large-ω-Precategory

  field
    preserves-id-structure-is-colax-functor-Noncoherent-Large-ω-Precategory :
      preserves-id-structure-map-Noncoherent-Large-ω-Precategory
        ( 𝒜)
        ( ℬ)
        ( F)

  field
    preserves-comp-structure-is-colax-functor-Noncoherent-Large-ω-Precategory :
      preserves-comp-structure-map-Noncoherent-Large-ω-Precategory
        ( 𝒜)
        ( ℬ)
        ( F)

  preserves-id-hom-is-colax-functor-Noncoherent-Large-ω-Precategory :
    {l : Level}
    (x : obj-Noncoherent-Large-ω-Precategory 𝒜 l) →
    2-hom-Noncoherent-Large-ω-Precategory ℬ
      ( hom-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ F
        ( id-hom-Noncoherent-Large-ω-Precategory 𝒜 {x = x}))
      ( id-hom-Noncoherent-Large-ω-Precategory ℬ
        { x = obj-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ F x})
  preserves-id-hom-is-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-refl-1-cell-is-colax-reflexive-large-globular-map
      preserves-id-structure-is-colax-functor-Noncoherent-Large-ω-Precategory

  preserves-id-structure-hom-is-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    preserves-id-structure-map-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        𝒜 x y)
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map F)
  preserves-id-structure-hom-is-colax-functor-Noncoherent-Large-ω-Precategory =
    is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-large-globular-map
      preserves-id-structure-is-colax-functor-Noncoherent-Large-ω-Precategory

  preserves-comp-hom-is-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2}
    {z : obj-Noncoherent-Large-ω-Precategory 𝒜 l3}
    (g : hom-Noncoherent-Large-ω-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Large-ω-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Large-ω-Precategory ℬ
      ( hom-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ F
        ( comp-hom-Noncoherent-Large-ω-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Large-ω-Precategory ℬ
        ( hom-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ F g)
        ( hom-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ F f))
  preserves-comp-hom-is-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-comp-1-cell-is-colax-transitive-large-globular-map
      preserves-comp-structure-is-colax-functor-Noncoherent-Large-ω-Precategory

  preserves-comp-structure-hom-is-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    preserves-comp-structure-map-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        𝒜 x y)
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map F)
  preserves-comp-structure-hom-is-colax-functor-Noncoherent-Large-ω-Precategory =
    is-colax-transitive-1-cell-globular-map-is-colax-transitive-large-globular-map
      preserves-comp-structure-is-colax-functor-Noncoherent-Large-ω-Precategory

  is-colax-functor-hom-is-colax-functor-map-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    is-colax-functor-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        𝒜 x y)
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map F)
  is-colax-functor-hom-is-colax-functor-map-Noncoherent-Large-ω-Precategory =
    make-is-colax-functor-Noncoherent-ω-Precategory
      preserves-id-structure-hom-is-colax-functor-Noncoherent-Large-ω-Precategory
      preserves-comp-structure-hom-is-colax-functor-Noncoherent-Large-ω-Precategory

open is-colax-functor-Noncoherent-Large-ω-Precategory public
```

### The type of colax functors between noncoherent ω-precategories

```agda
record
  colax-functor-Noncoherent-Large-ω-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  (δ : Level → Level)
  (𝒜 : Noncoherent-Large-ω-Precategory α1 β1)
  (ℬ : Noncoherent-Large-ω-Precategory α2 β2) : UUω
  where

  constructor
    make-colax-functor-Noncoherent-Large-ω-Precategory
```

The underlying large globular map of a colax functor:

```agda
  field
    map-colax-functor-Noncoherent-Large-ω-Precategory :
      map-Noncoherent-Large-ω-Precategory δ 𝒜 ℬ

  obj-colax-functor-Noncoherent-Large-ω-Precategory :
    {l : Level} →
    obj-Noncoherent-Large-ω-Precategory 𝒜 l →
    obj-Noncoherent-Large-ω-Precategory ℬ (δ l)
  obj-colax-functor-Noncoherent-Large-ω-Precategory =
    obj-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ
      ( map-colax-functor-Noncoherent-Large-ω-Precategory)

  hom-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    hom-Noncoherent-Large-ω-Precategory 𝒜 x y →
    hom-Noncoherent-Large-ω-Precategory ℬ
      ( obj-colax-functor-Noncoherent-Large-ω-Precategory x)
      ( obj-colax-functor-Noncoherent-Large-ω-Precategory y)
  hom-colax-functor-Noncoherent-Large-ω-Precategory =
    hom-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ
      map-colax-functor-Noncoherent-Large-ω-Precategory

  2-hom-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2}
    {f g : hom-Noncoherent-Large-ω-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Large-ω-Precategory 𝒜 f g →
    2-hom-Noncoherent-Large-ω-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-ω-Precategory f)
      ( hom-colax-functor-Noncoherent-Large-ω-Precategory g)
  2-hom-colax-functor-Noncoherent-Large-ω-Precategory =
    2-hom-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ
      map-colax-functor-Noncoherent-Large-ω-Precategory

  hom-globular-map-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    globular-map
      ( hom-globular-type-Noncoherent-Large-ω-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Large-ω-Precategory ℬ
        ( obj-colax-functor-Noncoherent-Large-ω-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-ω-Precategory y))
  hom-globular-map-colax-functor-Noncoherent-Large-ω-Precategory =
    hom-globular-map-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ
      ( map-colax-functor-Noncoherent-Large-ω-Precategory)

  field
    is-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory :
      is-colax-functor-Noncoherent-Large-ω-Precategory 𝒜 ℬ
        ( map-colax-functor-Noncoherent-Large-ω-Precategory)
```

Preservation of the identity structure:

```agda
  preserves-id-structure-colax-functor-Noncoherent-Large-ω-Precategory :
    preserves-id-structure-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ
      map-colax-functor-Noncoherent-Large-ω-Precategory
  preserves-id-structure-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-id-structure-is-colax-functor-Noncoherent-Large-ω-Precategory
      is-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory

  colax-reflexive-map-colax-functor-Noncoherent-Large-ω-Precategory :
    large-colax-reflexive-globular-map δ
      ( large-reflexive-globular-type-Noncoherent-Large-ω-Precategory
        𝒜)
      ( large-reflexive-globular-type-Noncoherent-Large-ω-Precategory
        ℬ)
  colax-reflexive-map-colax-functor-Noncoherent-Large-ω-Precategory =
    make-large-colax-reflexive-globular-map
      map-colax-functor-Noncoherent-Large-ω-Precategory
      preserves-id-structure-colax-functor-Noncoherent-Large-ω-Precategory

  preserves-id-hom-colax-functor-Noncoherent-Large-ω-Precategory :
    {l : Level}
    (x : obj-Noncoherent-Large-ω-Precategory 𝒜 l) →
    2-hom-Noncoherent-Large-ω-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-ω-Precategory
        ( id-hom-Noncoherent-Large-ω-Precategory 𝒜 {x = x}))
      ( id-hom-Noncoherent-Large-ω-Precategory ℬ
        { x = obj-colax-functor-Noncoherent-Large-ω-Precategory x})
  preserves-id-hom-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-id-hom-is-colax-functor-Noncoherent-Large-ω-Precategory
      ( is-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory)

  preserves-id-structure-hom-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    preserves-id-structure-map-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        𝒜 x y)
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map
        map-colax-functor-Noncoherent-Large-ω-Precategory)
  preserves-id-structure-hom-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-id-structure-hom-is-colax-functor-Noncoherent-Large-ω-Precategory
      is-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory
```

Preservation of the composition structure:

```agda
  preserves-comp-structure-colax-functor-Noncoherent-Large-ω-Precategory :
    preserves-comp-structure-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ
      map-colax-functor-Noncoherent-Large-ω-Precategory
  preserves-comp-structure-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-comp-structure-is-colax-functor-Noncoherent-Large-ω-Precategory
      is-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory

  colax-transitive-map-colax-functor-Noncoherent-Large-ω-Precategory :
    large-colax-transitive-globular-map δ
      ( large-transitive-globular-type-Noncoherent-Large-ω-Precategory
        𝒜)
      ( large-transitive-globular-type-Noncoherent-Large-ω-Precategory
        ℬ)
  large-globular-map-large-colax-transitive-globular-map
    colax-transitive-map-colax-functor-Noncoherent-Large-ω-Precategory =
    map-colax-functor-Noncoherent-Large-ω-Precategory
  is-colax-transitive-large-colax-transitive-globular-map
    colax-transitive-map-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-comp-structure-colax-functor-Noncoherent-Large-ω-Precategory

  preserves-comp-hom-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2}
    {z : obj-Noncoherent-Large-ω-Precategory 𝒜 l3}
    (g : hom-Noncoherent-Large-ω-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Large-ω-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Large-ω-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Large-ω-Precategory
        ( comp-hom-Noncoherent-Large-ω-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Large-ω-Precategory ℬ
        ( hom-colax-functor-Noncoherent-Large-ω-Precategory g)
        ( hom-colax-functor-Noncoherent-Large-ω-Precategory f))
  preserves-comp-hom-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-comp-hom-is-colax-functor-Noncoherent-Large-ω-Precategory
      ( is-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory)

  preserves-comp-structure-hom-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    preserves-comp-structure-map-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        𝒜 x y)
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map
        map-colax-functor-Noncoherent-Large-ω-Precategory)
  preserves-comp-structure-hom-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-comp-structure-hom-is-colax-functor-Noncoherent-Large-ω-Precategory
      is-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory
```

The globular map on hom-types is again a colax functor:

```agda
  is-colax-functor-hom-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2} →
    is-colax-functor-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Large-ω-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-ω-Precategory y))
      ( hom-globular-map-colax-functor-Noncoherent-Large-ω-Precategory)
  is-colax-functor-hom-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory =
    make-is-colax-functor-Noncoherent-ω-Precategory
      preserves-id-structure-hom-colax-functor-Noncoherent-Large-ω-Precategory
      preserves-comp-structure-hom-colax-functor-Noncoherent-Large-ω-Precategory

  hom-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-ω-Precategory 𝒜 l1)
    (y : obj-Noncoherent-Large-ω-Precategory 𝒜 l2) →
    colax-functor-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Large-ω-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-ω-Precategory y))
  hom-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory
    x y =
    hom-globular-map-colax-functor-Noncoherent-Large-ω-Precategory ,
    is-colax-functor-hom-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory

open colax-functor-Noncoherent-Large-ω-Precategory public
```

### The identity colax functor on a noncoherent large ω-precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (𝒜 : Noncoherent-Large-ω-Precategory α β)
  where

  preserves-id-structure-id-colax-functor-Noncoherent-Large-ω-Precatory :
    preserves-id-structure-map-Noncoherent-Large-ω-Precategory 𝒜 𝒜
      ( id-map-Noncoherent-Large-ω-Precategory 𝒜)
  preserves-id-structure-id-colax-functor-Noncoherent-Large-ω-Precatory =
    is-colax-reflexive-id-large-colax-reflexive-globular-map
      ( large-reflexive-globular-type-Noncoherent-Large-ω-Precategory
        𝒜)

  preserves-comp-structure-id-colax-functor-Noncoherent-Large-ω-Precategory :
    preserves-comp-structure-map-Noncoherent-Large-ω-Precategory 𝒜 𝒜
      ( id-map-Noncoherent-Large-ω-Precategory 𝒜)
  preserves-comp-1-cell-is-colax-transitive-large-globular-map
    preserves-comp-structure-id-colax-functor-Noncoherent-Large-ω-Precategory
      g f =
    id-2-hom-Noncoherent-Large-ω-Precategory 𝒜 _
  is-colax-transitive-1-cell-globular-map-is-colax-transitive-large-globular-map
    preserves-comp-structure-id-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-comp-structure-id-colax-functor-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        𝒜 _ _)

  is-colax-functor-id-colax-functor-Noncoherent-Large-ω-Precategory :
    is-colax-functor-Noncoherent-Large-ω-Precategory 𝒜 𝒜
      ( id-map-Noncoherent-Large-ω-Precategory 𝒜)
  is-colax-functor-id-colax-functor-Noncoherent-Large-ω-Precategory =
    make-is-colax-functor-Noncoherent-Large-ω-Precategory
      preserves-id-structure-id-colax-functor-Noncoherent-Large-ω-Precatory
      preserves-comp-structure-id-colax-functor-Noncoherent-Large-ω-Precategory

  id-colax-functor-Noncoherent-Large-ω-Precategory :
    colax-functor-Noncoherent-Large-ω-Precategory (λ l → l) 𝒜 𝒜
  map-colax-functor-Noncoherent-Large-ω-Precategory
    id-colax-functor-Noncoherent-Large-ω-Precategory =
    id-map-Noncoherent-Large-ω-Precategory 𝒜
  is-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory
    id-colax-functor-Noncoherent-Large-ω-Precategory =
    is-colax-functor-id-colax-functor-Noncoherent-Large-ω-Precategory
```

### Composition of colax functors between noncoherent ω-precategories

```agda
module _
  {α1 α2 α3 : Level → Level}
  {β1 β2 β3 : Level → Level → Level}
  {δ1 δ2 : Level → Level}
  {𝒜 : Noncoherent-Large-ω-Precategory α1 β1}
  {ℬ : Noncoherent-Large-ω-Precategory α2 β2}
  {𝒞 : Noncoherent-Large-ω-Precategory α3 β3}
  (G : colax-functor-Noncoherent-Large-ω-Precategory δ2 ℬ 𝒞)
  (F : colax-functor-Noncoherent-Large-ω-Precategory δ1 𝒜 ℬ)
  where

  map-comp-colax-functor-Noncoherent-Large-ω-Precategory :
    map-Noncoherent-Large-ω-Precategory (λ l → δ2 (δ1 l)) 𝒜 𝒞
  map-comp-colax-functor-Noncoherent-Large-ω-Precategory =
    comp-map-Noncoherent-Large-ω-Precategory 𝒜 ℬ 𝒞
      ( map-colax-functor-Noncoherent-Large-ω-Precategory G)
      ( map-colax-functor-Noncoherent-Large-ω-Precategory F)

  preserves-id-structure-comp-colax-functor-Noncoherent-Large-ω-Precategory :
    preserves-id-structure-map-Noncoherent-Large-ω-Precategory 𝒜 𝒞
      map-comp-colax-functor-Noncoherent-Large-ω-Precategory
  preserves-refl-1-cell-is-colax-reflexive-large-globular-map
    preserves-id-structure-comp-colax-functor-Noncoherent-Large-ω-Precategory
      x =
      comp-2-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( preserves-id-hom-colax-functor-Noncoherent-Large-ω-Precategory
          ( G)
          ( _))
        ( 2-hom-colax-functor-Noncoherent-Large-ω-Precategory G
          ( preserves-id-hom-colax-functor-Noncoherent-Large-ω-Precategory
            ( F)
            ( _)))
  is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-large-globular-map
    preserves-id-structure-comp-colax-functor-Noncoherent-Large-ω-Precategory =
    preserves-id-structure-comp-colax-functor-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        𝒜 _ _)
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ℬ _ _)
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        𝒞 _ _)
      ( hom-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory
        G _ _)
      ( hom-colax-functor-colax-functor-Noncoherent-Large-ω-Precategory
        F _ _)

  preserves-comp-structure-comp-colax-functor-Noncoherent-Large-ω-Precategory :
    preserves-comp-structure-map-Noncoherent-Large-ω-Precategory 𝒜 𝒞
      map-comp-colax-functor-Noncoherent-Large-ω-Precategory
  preserves-comp-structure-comp-colax-functor-Noncoherent-Large-ω-Precategory =
    is-colax-transitive-comp-large-colax-transitive-globular-map
      ( large-transitive-globular-type-Noncoherent-Large-ω-Precategory
        𝒜)
      ( large-transitive-globular-type-Noncoherent-Large-ω-Precategory
        ℬ)
      ( large-transitive-globular-type-Noncoherent-Large-ω-Precategory
        𝒞)
      ( colax-transitive-map-colax-functor-Noncoherent-Large-ω-Precategory
        G)
      ( colax-transitive-map-colax-functor-Noncoherent-Large-ω-Precategory
        F)

  is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Precategory :
    is-colax-functor-Noncoherent-Large-ω-Precategory 𝒜 𝒞
      map-comp-colax-functor-Noncoherent-Large-ω-Precategory
  is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Precategory =
    make-is-colax-functor-Noncoherent-Large-ω-Precategory
      preserves-id-structure-comp-colax-functor-Noncoherent-Large-ω-Precategory
      preserves-comp-structure-comp-colax-functor-Noncoherent-Large-ω-Precategory

  comp-colax-functor-Noncoherent-Large-Wild-Precategory :
    colax-functor-Noncoherent-Large-ω-Precategory
      ( λ l → δ2 (δ1 l))
      ( 𝒜)
      ( 𝒞)
  comp-colax-functor-Noncoherent-Large-Wild-Precategory =
    make-colax-functor-Noncoherent-Large-ω-Precategory
      map-comp-colax-functor-Noncoherent-Large-ω-Precategory
      is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Precategory
```

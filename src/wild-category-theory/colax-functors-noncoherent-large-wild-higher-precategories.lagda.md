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

open import structured-types.globular-maps
open import structured-types.globular-types
open import structured-types.large-colax-reflexive-globular-maps
open import structured-types.large-colax-transitive-globular-maps
open import structured-types.large-globular-maps

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

in `ℬ`, and for every pair of composable $(n+1)$-morphisms `g` after `f` in `𝒜`,
there is an $(n+2)$-morphism

```text
  Fₙ₊₁ (g ∘ f) ⇒ (Fₙ₊₁ g) ∘ (Fₙ₊₁ f)
```

in `ℬ`.

## Definitions

### The predicate on maps between large noncoherent wild higher precategories of preserving the identity structure

```agda
preserves-id-structure-map-Noncoherent-Large-Wild-Higher-Precategory :
  {α1 α2 γ : Level → Level}
  {β1 β2 : Level → Level → Level}
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2)
  (F : map-Noncoherent-Large-Wild-Higher-Precategory γ 𝒜 ℬ) → UUω
preserves-id-structure-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ F =
  is-colax-reflexive-large-globular-map
    ( large-reflexive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
      𝒜)
    ( large-reflexive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
      ℬ)
    ( F)
```

### The predicate on maps between large noncoherent wild higher precategories of preserving the composition structure

```agda
preserves-comp-structure-map-Noncoherent-Large-Wild-Higher-Precategory :
  {α1 α2 γ : Level → Level}
  {β1 β2 : Level → Level → Level}
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2)
  (F : map-Noncoherent-Large-Wild-Higher-Precategory γ 𝒜 ℬ) → UUω
preserves-comp-structure-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ F =
  is-colax-transitive-large-globular-map
    ( large-transitive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
      𝒜)
    ( large-transitive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
      ℬ)
    ( F)
```

### The predicate of being a colax functor between noncoherent wild higher precategories

```agda
record
  is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  {α1 α2 : Level → Level}
  {β1 β2 : Level → Level → Level}
  {γ : Level → Level}
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α1 β1)
  (ℬ : Noncoherent-Large-Wild-Higher-Precategory α2 β2)
  (F : map-Noncoherent-Large-Wild-Higher-Precategory γ 𝒜 ℬ) : UUω
  where

  field
    preserves-id-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
      preserves-id-structure-map-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒜)
        ( ℬ)
        ( F)

  field
    preserves-comp-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
      preserves-comp-structure-map-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒜)
        ( ℬ)
        ( F)

  preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l) →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
      ( hom-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ F
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 {x = x}))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
        { x = obj-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ F x})
  preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-refl-1-cell-is-colax-reflexive-large-globular-map
      preserves-id-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  preserves-id-structure-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    preserves-id-structure-map-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        𝒜 x y)
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map F)
  preserves-id-structure-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-large-globular-map
      preserves-id-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2}
    {z : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l3}
    (g : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
      ( hom-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ F
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory ℬ
        ( hom-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ F g)
        ( hom-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ F f))
  preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-1-cell-is-colax-transitive-large-globular-map
      preserves-comp-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  preserves-comp-structure-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    preserves-comp-structure-map-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        𝒜 x y)
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map F)
  preserves-comp-structure-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    is-colax-transitive-1-cell-globular-map-is-colax-transitive-large-globular-map
      preserves-comp-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  is-colax-functor-hom-is-colax-functor-map-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    is-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        𝒜 x y)
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map F)
  is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
    is-colax-functor-hom-is-colax-functor-map-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-id-structure-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
    is-colax-functor-hom-is-colax-functor-map-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-structure-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

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
```

- The underlying large globular map of a colax functor

```agda
  field
    map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
      map-Noncoherent-Large-Wild-Higher-Precategory δ 𝒜 ℬ

  obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l : Level} →
    obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l →
    obj-Noncoherent-Large-Wild-Higher-Precategory ℬ (δ l)
  obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    obj-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ
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
    hom-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ
      map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

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
    2-hom-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ
      map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  hom-globular-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    globular-map
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory ℬ
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory y))
  hom-globular-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    hom-globular-map-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)

  field
    is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
      is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ
        ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)
```

- Preservation of the identity structure

```agda
  preserves-id-structure-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    preserves-id-structure-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ
      map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  preserves-id-structure-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-id-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  colax-reflexive-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    large-colax-reflexive-globular-map δ
      ( large-reflexive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        𝒜)
      ( large-reflexive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        ℬ)
  large-globular-map-large-colax-reflexive-globular-map
    colax-reflexive-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  is-colax-reflexive-large-colax-reflexive-globular-map
    colax-reflexive-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-id-structure-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

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

  preserves-id-structure-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    preserves-id-structure-map-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        𝒜 x y)
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map
        map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)
  preserves-id-structure-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-id-structure-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
```

- Preservation of the composition structure

```agda
  preserves-comp-structure-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    preserves-comp-structure-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ
      map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  preserves-comp-structure-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  colax-transitive-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    large-colax-transitive-globular-map δ
      ( large-transitive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        𝒜)
      ( large-transitive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        ℬ)
  large-globular-map-large-colax-transitive-globular-map
    colax-transitive-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  is-colax-transitive-large-colax-transitive-globular-map
    colax-transitive-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-structure-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

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

  preserves-comp-structure-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    preserves-comp-structure-map-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        𝒜 x y)
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ℬ _ _)
      ( 1-cell-globular-map-large-globular-map
        map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)
  preserves-comp-structure-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-structure-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
```

- The globular map on hom-types is again a colax functor

```agda
  is-colax-functor-hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒜 l2} →
    is-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategory y))
      ( hom-globular-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory)
  is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
    is-colax-functor-hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-id-structure-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
    is-colax-functor-hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-structure-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
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
  pr1
    ( hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      x y) =
    hom-globular-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  pr2
    ( hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      x y) =
    is-colax-functor-hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

open colax-functor-Noncoherent-Large-Wild-Higher-Precategory public
```

### The identity colax functor on a noncoherent large wild higher precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (𝒜 : Noncoherent-Large-Wild-Higher-Precategory α β)
  where

  preserves-id-structure-id-colax-functor-Noncoherent-Large-Wild-Higher-Precatory :
    preserves-id-structure-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 𝒜
      ( id-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜)
  preserves-id-structure-id-colax-functor-Noncoherent-Large-Wild-Higher-Precatory =
    is-colax-reflexive-id-large-colax-reflexive-globular-map
      ( large-reflexive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        𝒜)

  preserves-comp-structure-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    preserves-comp-structure-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 𝒜
      ( id-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜)
  preserves-comp-1-cell-is-colax-transitive-large-globular-map
    preserves-comp-structure-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      g f =
    id-2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒜 _
  is-colax-transitive-1-cell-globular-map-is-colax-transitive-large-globular-map
    preserves-comp-structure-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        𝒜 _ _)

  is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory 𝒜 𝒜
      ( id-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜)
  preserves-id-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-id-structure-id-colax-functor-Noncoherent-Large-Wild-Higher-Precatory
  preserves-comp-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-comp-structure-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    colax-functor-Noncoherent-Large-Wild-Higher-Precategory (λ l → l) 𝒜 𝒜
  map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    id-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜
  is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    id-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
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
    comp-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 ℬ 𝒞
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory G)
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory F)

  preserves-id-structure-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    preserves-id-structure-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 𝒞
      map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  preserves-refl-1-cell-is-colax-reflexive-large-globular-map
    preserves-id-structure-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      x =
      comp-2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
          ( G)
          ( _))
        ( 2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory G
          ( preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
            ( F)
            ( _)))
  is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-large-globular-map
    preserves-id-structure-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    preserves-id-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        𝒜 _ _)
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ℬ _ _)
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        𝒞 _ _)
      ( hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        G _ _)
      ( hom-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        F _ _)

  preserves-comp-structure-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory :
    preserves-comp-structure-map-Noncoherent-Large-Wild-Higher-Precategory 𝒜 𝒞
      map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  preserves-comp-structure-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory =
    is-colax-transitive-comp-large-colax-transitive-globular-map
      ( large-transitive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        𝒜)
      ( large-transitive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        ℬ)
      ( large-transitive-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        𝒞)
      ( colax-transitive-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        G)
      ( colax-transitive-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
        F)

  is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Precategory :
    is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory 𝒜 𝒞
      map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  preserves-id-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Precategory =
    preserves-id-structure-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  preserves-comp-structure-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Precategory =
    preserves-comp-structure-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory

  comp-colax-functor-Noncoherent-Large-Wild-Precategory :
    colax-functor-Noncoherent-Large-Wild-Higher-Precategory
      ( λ l → δ2 (δ1 l))
      ( 𝒜)
      ( 𝒞)
  map-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    comp-colax-functor-Noncoherent-Large-Wild-Precategory =
    map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
  is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategory
    comp-colax-functor-Noncoherent-Large-Wild-Precategory =
    is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Precategory
```

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

open import structured-types.colax-reflexive-globular-maps
open import structured-types.colax-transitive-globular-maps
open import structured-types.globular-maps
open import structured-types.globular-types
open import structured-types.reflexive-globular-types

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
which is [colax reflexive](structured-types.colax-reflexive-globular-maps.md)
and [colax transitive](structured-types.colax-transitive-globular-maps.md). This
means that for every $n$-morphism `f` in `𝒜`, where we take $0$-morphisms to be
objects, there is an $(n+1)$-morphism

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

### The predicate on maps on noncoherent wild higher precategories of preserving identity structure

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4)
  (F : map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  preserves-id-structure-map-Noncoherent-Wild-Higher-Precategory :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-id-structure-map-Noncoherent-Wild-Higher-Precategory =
    is-colax-reflexive-globular-map
      ( reflexive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜)
      ( reflexive-globular-type-Noncoherent-Wild-Higher-Precategory ℬ)
      ( F)
```

### The predicate on maps of noncoherent wild higher precategories of preserving composition structure

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4)
  (F : map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  preserves-comp-structure-map-Noncoherent-Wild-Higher-Precategory :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-structure-map-Noncoherent-Wild-Higher-Precategory =
    is-colax-transitive-globular-map
      ( transitive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜)
      ( transitive-globular-type-Noncoherent-Wild-Higher-Precategory ℬ)
      ( F)
```

### The predicate of being a colax functor between noncoherent wild higher precategories

```agda
record
  is-colax-functor-Noncoherent-Wild-Higher-Precategory
    {l1 l2 l3 l4 : Level}
    (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
    (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4)
    (F : map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ) : UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive

  field
    is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
      preserves-id-structure-map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ F

  preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
    (x : obj-Noncoherent-Wild-Higher-Precategory 𝒜) →
    2-hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( 1-cell-globular-map F (id-hom-Noncoherent-Wild-Higher-Precategory 𝒜))
      ( id-hom-Noncoherent-Wild-Higher-Precategory ℬ)
  preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory =
    preserves-refl-1-cell-is-colax-reflexive-globular-map
      is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory

  is-reflexive-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    is-colax-reflexive-globular-map
      ( hom-reflexive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜 x y)
      ( hom-reflexive-globular-type-Noncoherent-Wild-Higher-Precategory ℬ
        ( 0-cell-globular-map F x)
        ( 0-cell-globular-map F y))
      ( 1-cell-globular-map-globular-map F)
  is-reflexive-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map
      is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory

  field
    is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
      preserves-comp-structure-map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ F

  preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y z : obj-Noncoherent-Wild-Higher-Precategory 𝒜}
    (g : hom-Noncoherent-Wild-Higher-Precategory 𝒜 y z)
    (f : hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y) →
    2-hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( 1-cell-globular-map F
        ( comp-hom-Noncoherent-Wild-Higher-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-Wild-Higher-Precategory ℬ
        ( 1-cell-globular-map F g)
        ( 1-cell-globular-map F f))
  preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategory =
    preserves-comp-1-cell-is-colax-transitive-globular-map
      is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory

  is-transitive-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    is-colax-transitive-globular-map
      ( hom-transitive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜 x y)
      ( hom-transitive-globular-type-Noncoherent-Wild-Higher-Precategory ℬ
        ( 0-cell-globular-map F x)
        ( 0-cell-globular-map F y))
      ( 1-cell-globular-map-globular-map F)
  is-transitive-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-colax-transitive-1-cell-globular-map-is-colax-transitive-globular-map
      is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory

  is-colax-functor-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    is-colax-functor-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        𝒜 x y)
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        ( ℬ)
        ( 0-cell-globular-map F x)
        ( 0-cell-globular-map F y))
      ( 1-cell-globular-map-globular-map F {x} {y})
  is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
    is-colax-functor-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-reflexive-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory
  is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
    is-colax-functor-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-transitive-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory

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
    ( is-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
```

**The action of colax functors on objects, morphisms, and higher morphisms**

```agda
module _
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2}
  {ℬ : Noncoherent-Wild-Higher-Precategory l3 l4}
  (F : colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  map-colax-functor-Noncoherent-Wild-Higher-Precategory :
    map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ
  map-colax-functor-Noncoherent-Wild-Higher-Precategory = pr1 F

  obj-colax-functor-Noncoherent-Wild-Higher-Precategory :
    obj-Noncoherent-Wild-Higher-Precategory 𝒜 →
    obj-Noncoherent-Wild-Higher-Precategory ℬ
  obj-colax-functor-Noncoherent-Wild-Higher-Precategory =
    0-cell-globular-map map-colax-functor-Noncoherent-Wild-Higher-Precategory

  hom-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y →
    hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory x)
      ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory y)
  hom-colax-functor-Noncoherent-Wild-Higher-Precategory =
    1-cell-globular-map map-colax-functor-Noncoherent-Wild-Higher-Precategory

  hom-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜} →
    globular-map
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategory ℬ
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory x)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategory y))
  hom-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory =
    1-cell-globular-map-globular-map
      map-colax-functor-Noncoherent-Wild-Higher-Precategory

  2-hom-colax-functor-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory 𝒜}
    {f g : hom-Noncoherent-Wild-Higher-Precategory 𝒜 x y} →
    2-hom-Noncoherent-Wild-Higher-Precategory 𝒜 f g →
    2-hom-Noncoherent-Wild-Higher-Precategory ℬ
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory f)
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategory g)
  2-hom-colax-functor-Noncoherent-Wild-Higher-Precategory =
    2-cell-globular-map map-colax-functor-Noncoherent-Wild-Higher-Precategory

  is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory :
    is-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory)
  is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory = pr2 F
```

**Preservation by colax functors of identity morphisms**

```agda
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

  colax-reflexive-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory :
    colax-reflexive-globular-map
      ( reflexive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜)
      ( reflexive-globular-type-Noncoherent-Wild-Higher-Precategory ℬ)
  colax-reflexive-globular-map.globular-map-colax-reflexive-globular-map
    colax-reflexive-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory =
    map-colax-functor-Noncoherent-Wild-Higher-Precategory
  colax-reflexive-globular-map.is-colax-reflexive-colax-reflexive-globular-map
    colax-reflexive-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
      is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory
```

**Preservation by colax functors of composition**

```agda
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

  colax-transitive-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory :
    colax-transitive-globular-map
      ( transitive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜)
      ( transitive-globular-type-Noncoherent-Wild-Higher-Precategory ℬ)
  globular-map-colax-transitive-globular-map
    colax-transitive-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory =
    map-colax-functor-Noncoherent-Wild-Higher-Precategory
  is-colax-transitive-colax-transitive-globular-map
    colax-transitive-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
      is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory
```

**The induced colax functor on the wild category of morphisms between two **
**objects**

```agda
  hom-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory :
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
  hom-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory x y =
    ( hom-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory ,
      is-colax-functor-hom-globular-map-is-colax-functor-Noncoherent-Wild-Higher-Precategory
        is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory)
```

### The identity colax functor on a noncoherent wild higher precategory

```agda
map-id-colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2) →
  map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒜
map-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 =
  id-map-Noncoherent-Wild-Higher-Precategory 𝒜

preserves-id-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2) →
  preserves-id-structure-map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒜
    ( map-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜)
preserves-id-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 =
  is-colax-reflexive-id-colax-reflexive-globular-map
    ( reflexive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜)

preserves-comp-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2) →
  preserves-comp-structure-map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒜
    ( map-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜)
preserves-comp-1-cell-is-colax-transitive-globular-map
  ( preserves-comp-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory
    𝒜)
  _ _ =
  id-2-hom-Noncoherent-Wild-Higher-Precategory 𝒜
is-colax-transitive-1-cell-globular-map-is-colax-transitive-globular-map
  ( preserves-comp-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory
    𝒜) =
  preserves-comp-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory
    ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
      ( 𝒜)
      ( _)
      ( _))

is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2) →
  is-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 𝒜
    ( map-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜)
is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
  ( is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜) =
  preserves-id-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜
is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
  ( is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜) =
  preserves-comp-structure-id-colax-functor-Noncoherent-Wild-Higher-Precategory
    𝒜

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
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4)
  (𝒞 : Noncoherent-Wild-Higher-Precategory l5 l6)
  (G : colax-functor-Noncoherent-Wild-Higher-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory :
    map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒞
  map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    comp-map-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ 𝒞
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory G)
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategory F)

preserves-id-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4)
  (𝒞 : Noncoherent-Wild-Higher-Precategory l5 l6)
  (G : colax-functor-Noncoherent-Wild-Higher-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ) →
  preserves-id-structure-map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒞
    ( map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ 𝒞 G F)
preserves-refl-1-cell-is-colax-reflexive-globular-map
  ( preserves-id-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
    𝒜 ℬ 𝒞 G F)
    x =
  comp-2-hom-Noncoherent-Wild-Higher-Precategory 𝒞
    ( preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategory G _)
    ( 2-hom-colax-functor-Noncoherent-Wild-Higher-Precategory G
      ( preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategory F _))
is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map
  ( preserves-id-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
    𝒜 ℬ 𝒞 G F) =
  preserves-id-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
    ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
        𝒜 _ _)
    ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
      ℬ _ _)
    ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
      𝒞 _ _)
    ( hom-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory
      G _ _)
    ( hom-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategory
      F _ _)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒜 : Noncoherent-Wild-Higher-Precategory l1 l2)
  (ℬ : Noncoherent-Wild-Higher-Precategory l3 l4)
  (𝒞 : Noncoherent-Wild-Higher-Precategory l5 l6)
  (G : colax-functor-Noncoherent-Wild-Higher-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ)
  where

  preserves-comp-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory :
    preserves-comp-structure-map-Noncoherent-Wild-Higher-Precategory 𝒜 𝒞
      ( map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ 𝒞 G F)
  preserves-comp-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-colax-transitive-comp-colax-transitive-globular-map
      ( transitive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒜)
      ( transitive-globular-type-Noncoherent-Wild-Higher-Precategory ℬ)
      ( transitive-globular-type-Noncoherent-Wild-Higher-Precategory 𝒞)
        ( colax-transitive-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory
        G)
      ( colax-transitive-globular-map-colax-functor-Noncoherent-Wild-Higher-Precategory
        F)

  is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory :
    is-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 𝒞
      ( map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ 𝒞 G F)
  is-reflexive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
    is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    preserves-id-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
      𝒜 ℬ 𝒞 G F
  is-transitive-is-colax-functor-Noncoherent-Wild-Higher-Precategory
    is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    preserves-comp-structure-comp-colax-functor-Noncoherent-Wild-Higher-Precategory

  comp-colax-functor-Noncoherent-Wild-Higher-Precategory :
    colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 𝒞
  pr1 comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    map-comp-colax-functor-Noncoherent-Wild-Higher-Precategory 𝒜 ℬ 𝒞 G F
  pr2 comp-colax-functor-Noncoherent-Wild-Higher-Precategory =
    is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategory
```

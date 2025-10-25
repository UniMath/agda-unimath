# Colax functors between noncoherent ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.colax-functors-noncoherent-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.colax-reflexive-globular-maps
open import globular-types.colax-transitive-globular-maps
open import globular-types.globular-maps
open import globular-types.globular-types
open import globular-types.reflexive-globular-types

open import wild-category-theory.maps-noncoherent-omega-precategories
open import wild-category-theory.noncoherent-omega-precategories
```

</details>

## Idea

A
{{#concept "colax functor" Disambiguation="between noncoherent ω-precategories" Agda=colax-functor-Noncoherent-ω-Precategory}}
`F` between
[noncoherent ω-precategories](wild-category-theory.noncoherent-omega-precategories.md)
`𝒜` and `ℬ` is a
[map of noncoherent ω-precategories](wild-category-theory.maps-noncoherent-omega-precategories.md)
which is [colax reflexive](globular-types.colax-reflexive-globular-maps.md) and
[colax transitive](globular-types.colax-transitive-globular-maps.md). This means
that for every $n$-morphism `f` in `𝒜`, where we take $0$-morphisms to be
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

### The predicate on maps on noncoherent ω-precategories of preserving identity structure

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4)
  (F : map-Noncoherent-ω-Precategory 𝒜 ℬ)
  where

  preserves-id-structure-map-Noncoherent-ω-Precategory :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-id-structure-map-Noncoherent-ω-Precategory =
    is-colax-reflexive-globular-map
      ( reflexive-globular-type-Noncoherent-ω-Precategory 𝒜)
      ( reflexive-globular-type-Noncoherent-ω-Precategory ℬ)
      ( F)
```

### The predicate on maps of noncoherent ω-precategories of preserving composition structure

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4)
  (F : map-Noncoherent-ω-Precategory 𝒜 ℬ)
  where

  preserves-comp-structure-map-Noncoherent-ω-Precategory :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-structure-map-Noncoherent-ω-Precategory =
    is-colax-transitive-globular-map
      ( transitive-globular-type-Noncoherent-ω-Precategory 𝒜)
      ( transitive-globular-type-Noncoherent-ω-Precategory ℬ)
      ( F)
```

### The predicate of being a colax functor between noncoherent ω-precategories

```agda
record
  is-colax-functor-Noncoherent-ω-Precategory
    {l1 l2 l3 l4 : Level}
    (𝒜 : Noncoherent-ω-Precategory l1 l2)
    (ℬ : Noncoherent-ω-Precategory l3 l4)
    (F : map-Noncoherent-ω-Precategory 𝒜 ℬ) : UU (l1 ⊔ l2 ⊔ l4)
  where

  constructor make-is-colax-functor-Noncoherent-ω-Precategory

  coinductive

  field
    is-reflexive-is-colax-functor-Noncoherent-ω-Precategory :
      preserves-id-structure-map-Noncoherent-ω-Precategory 𝒜 ℬ F

  preserves-id-hom-is-colax-functor-Noncoherent-ω-Precategory :
    (x : obj-Noncoherent-ω-Precategory 𝒜) →
    2-hom-Noncoherent-ω-Precategory ℬ
      ( 1-cell-globular-map F (id-hom-Noncoherent-ω-Precategory 𝒜))
      ( id-hom-Noncoherent-ω-Precategory ℬ)
  preserves-id-hom-is-colax-functor-Noncoherent-ω-Precategory =
    preserves-refl-1-cell-is-colax-reflexive-globular-map
      is-reflexive-is-colax-functor-Noncoherent-ω-Precategory

  is-reflexive-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜} →
    is-colax-reflexive-globular-map
      ( hom-reflexive-globular-type-Noncoherent-ω-Precategory 𝒜 x y)
      ( hom-reflexive-globular-type-Noncoherent-ω-Precategory ℬ
        ( 0-cell-globular-map F x)
        ( 0-cell-globular-map F y))
      ( 1-cell-globular-map-globular-map F)
  is-reflexive-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory =
    is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map
      is-reflexive-is-colax-functor-Noncoherent-ω-Precategory

  field
    is-transitive-is-colax-functor-Noncoherent-ω-Precategory :
      preserves-comp-structure-map-Noncoherent-ω-Precategory 𝒜 ℬ F

  preserves-comp-hom-is-colax-functor-Noncoherent-ω-Precategory :
    {x y z : obj-Noncoherent-ω-Precategory 𝒜}
    (g : hom-Noncoherent-ω-Precategory 𝒜 y z)
    (f : hom-Noncoherent-ω-Precategory 𝒜 x y) →
    2-hom-Noncoherent-ω-Precategory ℬ
      ( 1-cell-globular-map F
        ( comp-hom-Noncoherent-ω-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-ω-Precategory ℬ
        ( 1-cell-globular-map F g)
        ( 1-cell-globular-map F f))
  preserves-comp-hom-is-colax-functor-Noncoherent-ω-Precategory =
    preserves-comp-1-cell-is-colax-transitive-globular-map
      is-transitive-is-colax-functor-Noncoherent-ω-Precategory

  is-transitive-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜} →
    is-colax-transitive-globular-map
      ( hom-transitive-globular-type-Noncoherent-ω-Precategory 𝒜 x y)
      ( hom-transitive-globular-type-Noncoherent-ω-Precategory ℬ
        ( 0-cell-globular-map F x)
        ( 0-cell-globular-map F y))
      ( 1-cell-globular-map-globular-map F)
  is-transitive-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory =
    is-colax-transitive-1-cell-globular-map-is-colax-transitive-globular-map
      is-transitive-is-colax-functor-Noncoherent-ω-Precategory

  is-colax-functor-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜} →
    is-colax-functor-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        𝒜 x y)
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( ℬ)
        ( 0-cell-globular-map F x)
        ( 0-cell-globular-map F y))
      ( 1-cell-globular-map-globular-map F {x} {y})
  is-reflexive-is-colax-functor-Noncoherent-ω-Precategory
    is-colax-functor-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory =
    is-reflexive-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory
  is-transitive-is-colax-functor-Noncoherent-ω-Precategory
    is-colax-functor-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory =
    is-transitive-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory

open is-colax-functor-Noncoherent-ω-Precategory public
```

### The type of colax functors between noncoherent ω-precategories

```agda
colax-functor-Noncoherent-ω-Precategory :
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ =
  Σ ( map-Noncoherent-ω-Precategory 𝒜 ℬ)
    ( is-colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ)
```

The action of colax functors on objects, morphisms, and higher morphisms:

```agda
module _
  {l1 l2 l3 l4 : Level}
  {𝒜 : Noncoherent-ω-Precategory l1 l2}
  {ℬ : Noncoherent-ω-Precategory l3 l4}
  (F : colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ)
  where

  map-colax-functor-Noncoherent-ω-Precategory :
    map-Noncoherent-ω-Precategory 𝒜 ℬ
  map-colax-functor-Noncoherent-ω-Precategory = pr1 F

  obj-colax-functor-Noncoherent-ω-Precategory :
    obj-Noncoherent-ω-Precategory 𝒜 →
    obj-Noncoherent-ω-Precategory ℬ
  obj-colax-functor-Noncoherent-ω-Precategory =
    0-cell-globular-map map-colax-functor-Noncoherent-ω-Precategory

  hom-colax-functor-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜} →
    hom-Noncoherent-ω-Precategory 𝒜 x y →
    hom-Noncoherent-ω-Precategory ℬ
      ( obj-colax-functor-Noncoherent-ω-Precategory x)
      ( obj-colax-functor-Noncoherent-ω-Precategory y)
  hom-colax-functor-Noncoherent-ω-Precategory =
    1-cell-globular-map map-colax-functor-Noncoherent-ω-Precategory

  hom-globular-map-colax-functor-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜} →
    globular-map
      ( hom-globular-type-Noncoherent-ω-Precategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-ω-Precategory ℬ
        ( obj-colax-functor-Noncoherent-ω-Precategory x)
        ( obj-colax-functor-Noncoherent-ω-Precategory y))
  hom-globular-map-colax-functor-Noncoherent-ω-Precategory =
    1-cell-globular-map-globular-map
      map-colax-functor-Noncoherent-ω-Precategory

  2-hom-colax-functor-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory 𝒜}
    {f g : hom-Noncoherent-ω-Precategory 𝒜 x y} →
    2-hom-Noncoherent-ω-Precategory 𝒜 f g →
    2-hom-Noncoherent-ω-Precategory ℬ
      ( hom-colax-functor-Noncoherent-ω-Precategory f)
      ( hom-colax-functor-Noncoherent-ω-Precategory g)
  2-hom-colax-functor-Noncoherent-ω-Precategory =
    2-cell-globular-map map-colax-functor-Noncoherent-ω-Precategory

  is-colax-functor-colax-functor-Noncoherent-ω-Precategory :
    is-colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ
      ( map-colax-functor-Noncoherent-ω-Precategory)
  is-colax-functor-colax-functor-Noncoherent-ω-Precategory = pr2 F
```

Preservation by colax functors of identity morphisms:

```agda
  preserves-id-hom-colax-functor-Noncoherent-ω-Precategory :
    (x : obj-Noncoherent-ω-Precategory 𝒜) →
    2-hom-Noncoherent-ω-Precategory ℬ
      ( hom-colax-functor-Noncoherent-ω-Precategory
        ( id-hom-Noncoherent-ω-Precategory 𝒜 {x}))
      ( id-hom-Noncoherent-ω-Precategory ℬ
        { obj-colax-functor-Noncoherent-ω-Precategory x})
  preserves-id-hom-colax-functor-Noncoherent-ω-Precategory =
    preserves-id-hom-is-colax-functor-Noncoherent-ω-Precategory
      ( is-colax-functor-colax-functor-Noncoherent-ω-Precategory)

  colax-reflexive-globular-map-colax-functor-Noncoherent-ω-Precategory :
    colax-reflexive-globular-map
      ( reflexive-globular-type-Noncoherent-ω-Precategory 𝒜)
      ( reflexive-globular-type-Noncoherent-ω-Precategory ℬ)
  colax-reflexive-globular-map-colax-functor-Noncoherent-ω-Precategory =
    make-colax-reflexive-globular-map
      ( map-colax-functor-Noncoherent-ω-Precategory)
      ( is-reflexive-is-colax-functor-Noncoherent-ω-Precategory
        is-colax-functor-colax-functor-Noncoherent-ω-Precategory)
```

Preservation by colax functors of composition:

```agda
  preserves-comp-hom-colax-functor-Noncoherent-ω-Precategory :
    {x y z : obj-Noncoherent-ω-Precategory 𝒜}
    (g : hom-Noncoherent-ω-Precategory 𝒜 y z)
    (f : hom-Noncoherent-ω-Precategory 𝒜 x y) →
    2-hom-Noncoherent-ω-Precategory ℬ
      ( hom-colax-functor-Noncoherent-ω-Precategory
        ( comp-hom-Noncoherent-ω-Precategory 𝒜 g f))
      ( comp-hom-Noncoherent-ω-Precategory ℬ
        ( hom-colax-functor-Noncoherent-ω-Precategory g)
        ( hom-colax-functor-Noncoherent-ω-Precategory f))
  preserves-comp-hom-colax-functor-Noncoherent-ω-Precategory =
    preserves-comp-hom-is-colax-functor-Noncoherent-ω-Precategory
      ( is-colax-functor-colax-functor-Noncoherent-ω-Precategory)

  colax-transitive-globular-map-colax-functor-Noncoherent-ω-Precategory :
    colax-transitive-globular-map
      ( transitive-globular-type-Noncoherent-ω-Precategory 𝒜)
      ( transitive-globular-type-Noncoherent-ω-Precategory ℬ)
  colax-transitive-globular-map-colax-functor-Noncoherent-ω-Precategory =
    make-colax-transitive-globular-map
      ( map-colax-functor-Noncoherent-ω-Precategory)
      ( is-transitive-is-colax-functor-Noncoherent-ω-Precategory
        is-colax-functor-colax-functor-Noncoherent-ω-Precategory)
```

The induced colax functor on the wild category of morphisms between two objects:

```agda
  hom-colax-functor-colax-functor-Noncoherent-ω-Precategory :
    (x y : obj-Noncoherent-ω-Precategory 𝒜) →
    colax-functor-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( ℬ)
        ( obj-colax-functor-Noncoherent-ω-Precategory x)
        ( obj-colax-functor-Noncoherent-ω-Precategory y))
  hom-colax-functor-colax-functor-Noncoherent-ω-Precategory x y =
    ( hom-globular-map-colax-functor-Noncoherent-ω-Precategory ,
      is-colax-functor-hom-globular-map-is-colax-functor-Noncoherent-ω-Precategory
        is-colax-functor-colax-functor-Noncoherent-ω-Precategory)
```

### The identity colax functor on a noncoherent ω-precategory

```agda
map-id-colax-functor-Noncoherent-ω-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-ω-Precategory l1 l2) →
  map-Noncoherent-ω-Precategory 𝒜 𝒜
map-id-colax-functor-Noncoherent-ω-Precategory 𝒜 =
  id-map-Noncoherent-ω-Precategory 𝒜

preserves-id-structure-id-colax-functor-Noncoherent-ω-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-ω-Precategory l1 l2) →
  preserves-id-structure-map-Noncoherent-ω-Precategory 𝒜 𝒜
    ( map-id-colax-functor-Noncoherent-ω-Precategory 𝒜)
preserves-id-structure-id-colax-functor-Noncoherent-ω-Precategory 𝒜 =
  is-colax-reflexive-id-colax-reflexive-globular-map
    ( reflexive-globular-type-Noncoherent-ω-Precategory 𝒜)

preserves-comp-structure-id-colax-functor-Noncoherent-ω-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-ω-Precategory l1 l2) →
  preserves-comp-structure-map-Noncoherent-ω-Precategory 𝒜 𝒜
    ( map-id-colax-functor-Noncoherent-ω-Precategory 𝒜)
preserves-comp-1-cell-is-colax-transitive-globular-map
  ( preserves-comp-structure-id-colax-functor-Noncoherent-ω-Precategory
    𝒜)
  _ _ =
  id-2-hom-Noncoherent-ω-Precategory 𝒜
is-colax-transitive-1-cell-globular-map-is-colax-transitive-globular-map
  ( preserves-comp-structure-id-colax-functor-Noncoherent-ω-Precategory
    𝒜) =
  preserves-comp-structure-id-colax-functor-Noncoherent-ω-Precategory
    ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
      ( 𝒜)
      ( _)
      ( _))

is-colax-functor-id-colax-functor-Noncoherent-ω-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-ω-Precategory l1 l2) →
  is-colax-functor-Noncoherent-ω-Precategory 𝒜 𝒜
    ( map-id-colax-functor-Noncoherent-ω-Precategory 𝒜)
is-colax-functor-id-colax-functor-Noncoherent-ω-Precategory 𝒜 =
  make-is-colax-functor-Noncoherent-ω-Precategory
    ( preserves-id-structure-id-colax-functor-Noncoherent-ω-Precategory
      𝒜)
    ( preserves-comp-structure-id-colax-functor-Noncoherent-ω-Precategory
      𝒜)

id-colax-functor-Noncoherent-ω-Precategory :
  {l1 l2 : Level} (𝒜 : Noncoherent-ω-Precategory l1 l2) →
  colax-functor-Noncoherent-ω-Precategory 𝒜 𝒜
id-colax-functor-Noncoherent-ω-Precategory 𝒜 =
  ( id-map-Noncoherent-ω-Precategory 𝒜 ,
    is-colax-functor-id-colax-functor-Noncoherent-ω-Precategory 𝒜)
```

### Composition of colax functors between noncoherent ω-precategories

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4)
  (𝒞 : Noncoherent-ω-Precategory l5 l6)
  (G : colax-functor-Noncoherent-ω-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ)
  where

  map-comp-colax-functor-Noncoherent-ω-Precategory :
    map-Noncoherent-ω-Precategory 𝒜 𝒞
  map-comp-colax-functor-Noncoherent-ω-Precategory =
    comp-map-Noncoherent-ω-Precategory 𝒜 ℬ 𝒞
      ( map-colax-functor-Noncoherent-ω-Precategory G)
      ( map-colax-functor-Noncoherent-ω-Precategory F)

preserves-id-structure-comp-colax-functor-Noncoherent-ω-Precategory :
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4)
  (𝒞 : Noncoherent-ω-Precategory l5 l6)
  (G : colax-functor-Noncoherent-ω-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ) →
  preserves-id-structure-map-Noncoherent-ω-Precategory 𝒜 𝒞
    ( map-comp-colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ 𝒞 G F)
preserves-refl-1-cell-is-colax-reflexive-globular-map
  ( preserves-id-structure-comp-colax-functor-Noncoherent-ω-Precategory
    𝒜 ℬ 𝒞 G F)
    x =
  comp-2-hom-Noncoherent-ω-Precategory 𝒞
    ( preserves-id-hom-colax-functor-Noncoherent-ω-Precategory G _)
    ( 2-hom-colax-functor-Noncoherent-ω-Precategory G
      ( preserves-id-hom-colax-functor-Noncoherent-ω-Precategory F _))
is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map
  ( preserves-id-structure-comp-colax-functor-Noncoherent-ω-Precategory
    𝒜 ℬ 𝒞 G F) =
  preserves-id-structure-comp-colax-functor-Noncoherent-ω-Precategory
    ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        𝒜 _ _)
    ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
      ℬ _ _)
    ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
      𝒞 _ _)
    ( hom-colax-functor-colax-functor-Noncoherent-ω-Precategory
      G _ _)
    ( hom-colax-functor-colax-functor-Noncoherent-ω-Precategory
      F _ _)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒜 : Noncoherent-ω-Precategory l1 l2)
  (ℬ : Noncoherent-ω-Precategory l3 l4)
  (𝒞 : Noncoherent-ω-Precategory l5 l6)
  (G : colax-functor-Noncoherent-ω-Precategory ℬ 𝒞)
  (F : colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ)
  where

  preserves-comp-structure-comp-colax-functor-Noncoherent-ω-Precategory :
    preserves-comp-structure-map-Noncoherent-ω-Precategory 𝒜 𝒞
      ( map-comp-colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ 𝒞 G F)
  preserves-comp-structure-comp-colax-functor-Noncoherent-ω-Precategory =
    is-colax-transitive-comp-colax-transitive-globular-map
      ( transitive-globular-type-Noncoherent-ω-Precategory 𝒜)
      ( transitive-globular-type-Noncoherent-ω-Precategory ℬ)
      ( transitive-globular-type-Noncoherent-ω-Precategory 𝒞)
        ( colax-transitive-globular-map-colax-functor-Noncoherent-ω-Precategory
        G)
      ( colax-transitive-globular-map-colax-functor-Noncoherent-ω-Precategory
        F)

  is-colax-functor-comp-colax-functor-Noncoherent-ω-Precategory :
    is-colax-functor-Noncoherent-ω-Precategory 𝒜 𝒞
      ( map-comp-colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ 𝒞 G F)
  is-colax-functor-comp-colax-functor-Noncoherent-ω-Precategory =
    make-is-colax-functor-Noncoherent-ω-Precategory
      ( preserves-id-structure-comp-colax-functor-Noncoherent-ω-Precategory
        𝒜 ℬ 𝒞 G F)
      ( preserves-comp-structure-comp-colax-functor-Noncoherent-ω-Precategory)

  comp-colax-functor-Noncoherent-ω-Precategory :
    colax-functor-Noncoherent-ω-Precategory 𝒜 𝒞
  pr1 comp-colax-functor-Noncoherent-ω-Precategory =
    map-comp-colax-functor-Noncoherent-ω-Precategory 𝒜 ℬ 𝒞 G F
  pr2 comp-colax-functor-Noncoherent-ω-Precategory =
    is-colax-functor-comp-colax-functor-Noncoherent-ω-Precategory
```

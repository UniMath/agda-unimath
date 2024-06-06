# Restrictions of functors to cores of precategories

```agda
module category-theory.restrictions-functors-cores-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cores-precategories
open import category-theory.faithful-functors-precategories
open import category-theory.fully-faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.precategories
open import category-theory.pseudomonic-functors-precategories

open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

For every [functor](category-theory.functors-precategories.md) `F : C → D` there
is a restriction functor between their
[cores](category-theory.cores-precategories.md)

```text
  core F : core C → core D
```

that fit into a natural diagram

```text
          core F
  core C ───────> core D
    │               │
    │               │
    │               │
    │               │
    ∨               ∨
    C ────────────> D.
            F
```

## Definitions

### Restrictions of functors to cores of precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  obj-functor-core-Precategory :
    obj-Precategory (core-precategory-Precategory C) →
    obj-Precategory (core-precategory-Precategory D)
  obj-functor-core-Precategory = obj-functor-Precategory C D F

  hom-functor-core-Precategory :
    {x y : obj-Precategory (core-precategory-Precategory C)} →
    hom-Precategory (core-precategory-Precategory C) x y →
    hom-Precategory
      ( core-precategory-Precategory D)
      ( obj-functor-core-Precategory x)
      ( obj-functor-core-Precategory y)
  hom-functor-core-Precategory = preserves-iso-functor-Precategory C D F

  map-functor-core-Precategory :
    map-Precategory
      ( core-precategory-Precategory C)
      ( core-precategory-Precategory D)
  pr1 map-functor-core-Precategory = obj-functor-core-Precategory
  pr2 map-functor-core-Precategory = hom-functor-core-Precategory

  preserves-id-functor-core-Precategory :
    preserves-id-hom-map-Precategory
      ( core-precategory-Precategory C)
      ( core-precategory-Precategory D)
      ( map-functor-core-Precategory)
  preserves-id-functor-core-Precategory x =
    eq-type-subtype
      ( is-iso-prop-Precategory D)
      ( preserves-id-functor-Precategory C D F x)

  preserves-comp-functor-core-Precategory :
    preserves-comp-hom-map-Precategory
      ( core-precategory-Precategory C)
      ( core-precategory-Precategory D)
      ( map-functor-core-Precategory)
  preserves-comp-functor-core-Precategory g f =
    eq-type-subtype
      ( is-iso-prop-Precategory D)
      ( preserves-comp-functor-Precategory C D F
        ( hom-iso-Precategory C g)
        ( hom-iso-Precategory C f))

  is-functor-functor-core-Precategory :
    is-functor-map-Precategory
      ( core-precategory-Precategory C)
      ( core-precategory-Precategory D)
      map-functor-core-Precategory
  pr1 is-functor-functor-core-Precategory =
    preserves-comp-functor-core-Precategory
  pr2 is-functor-functor-core-Precategory =
    preserves-id-functor-core-Precategory

  functor-core-Precategory :
    functor-Precategory
      ( core-precategory-Precategory C)
      ( core-precategory-Precategory D)
  pr1 functor-core-Precategory = obj-functor-core-Precategory
  pr1 (pr2 functor-core-Precategory) = hom-functor-core-Precategory
  pr2 (pr2 functor-core-Precategory) = is-functor-functor-core-Precategory
```

## Properties

### Faithful functors restrict to faithful functors on the core

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  is-faithful-functor-core-is-faithful-functor-Precategory :
    (F : functor-Precategory C D) →
    is-faithful-functor-Precategory C D F →
    is-faithful-functor-Precategory
      ( core-precategory-Precategory C)
      ( core-precategory-Precategory D)
      ( functor-core-Precategory C D F)
  is-faithful-functor-core-is-faithful-functor-Precategory =
    is-faithful-on-isos-is-faithful-functor-Precategory C D
```

### Pseudomonic functors restrict to fully faithful functors on the core

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (is-pseudomonic-F : is-pseudomonic-functor-Precategory C D F)
  where

  is-fully-faithful-functor-core-is-pseudomonic-functor-Precategory :
    is-fully-faithful-functor-Precategory
      ( core-precategory-Precategory C)
      ( core-precategory-Precategory D)
      ( functor-core-Precategory C D F)
  is-fully-faithful-functor-core-is-pseudomonic-functor-Precategory x y =
    is-equiv-preserves-iso-is-pseudomonic-functor-Precategory
      C D F is-pseudomonic-F
```

### Fully faithful functors restrict to fully faithful functors on the core

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (is-ff-F : is-fully-faithful-functor-Precategory C D F)
  where

  is-fully-faithful-functor-core-is-fully-faithful-functor-Precategory :
    is-fully-faithful-functor-Precategory
      ( core-precategory-Precategory C)
      ( core-precategory-Precategory D)
      ( functor-core-Precategory C D F)
  is-fully-faithful-functor-core-is-fully-faithful-functor-Precategory =
    is-fully-faithful-functor-core-is-pseudomonic-functor-Precategory C D F
      ( is-pseudomonic-is-fully-faithful-functor-Precategory C D F is-ff-F)
```

## External links

- [The core of a category](https://1lab.dev/Cat.Instances.Core.html) at 1lab
- [core groupoid](https://ncatlab.org/nlab/show/core+groupoid) at $n$Lab

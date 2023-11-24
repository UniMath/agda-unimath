# Constant functors

```agda
module category-theory.constant-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.functors-large-categories
open import category-theory.functors-large-precategories
open import category-theory.functors-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **constant functor** is a [functor](category-theory.functors-categories.md)
`F : C → D` that is constant at an object `d ∈ D` and the identity morphism at
that object.

## Definition

### Constant functors between precategories

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (d : obj-Precategory D)
  where

  constant-functor-Precategory : functor-Precategory C D
  pr1 constant-functor-Precategory _ = d
  pr1 (pr2 constant-functor-Precategory) _ = id-hom-Precategory D
  pr1 (pr2 (pr2 constant-functor-Precategory)) _ _ =
    inv (left-unit-law-comp-hom-Precategory D (id-hom-Precategory D))
  pr2 (pr2 (pr2 constant-functor-Precategory)) = refl-htpy
```

### Constant functors between categories

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Category l1 l2) (D : Category l3 l4)
  (d : obj-Category D)
  where

  constant-functor-Category : functor-Category C D
  constant-functor-Category =
    constant-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( d)
```

### Constant functors between large precategories

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  {l : Level} (d : obj-Large-Precategory D l)
  where

  constant-functor-Large-Precategory : functor-Large-Precategory (λ _ → l) C D
  obj-functor-Large-Precategory constant-functor-Large-Precategory _ = d
  hom-functor-Large-Precategory constant-functor-Large-Precategory _ =
    id-hom-Large-Precategory D
  preserves-comp-functor-Large-Precategory constant-functor-Large-Precategory
    _ _ =
    inv
      ( left-unit-law-comp-hom-Large-Precategory D (id-hom-Large-Precategory D))
  preserves-id-functor-Large-Precategory constant-functor-Large-Precategory =
    refl
```

### Constant functors between large categories

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Category αC βC) (D : Large-Category αD βD)
  {l : Level} (d : obj-Large-Category D l)
  where

  constant-functor-Large-Category : functor-Large-Category (λ _ → l) C D
  constant-functor-Large-Category =
    constant-functor-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( d)
```

## External links

- [constant functor](https://ncatlab.org/nlab/show/constant+functor) at $n$Lab

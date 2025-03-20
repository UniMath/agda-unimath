# Cores of categories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.cores-categories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext
open import category-theory.cores-precategories funext
open import category-theory.groupoids funext
open import category-theory.isomorphisms-in-categories funext
open import category-theory.precategories funext
open import category-theory.pregroupoids funext
open import category-theory.subcategories funext
open import category-theory.wide-subcategories funext

open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.universe-levels
```

</details>

## Idea

The **core of a [category](category-theory.categories.md)** `C` is the maximal
subgroupoid of it. It consists of all objects and
[isomorphisms](category-theory.isomorphisms-in-categories.md) in `C`.

## Definitions

### The core wide subcategory

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  core-wide-subcategory-Category : Wide-Subcategory l2 C
  core-wide-subcategory-Category =
    core-wide-subprecategory-Precategory (precategory-Category C)
```

### The core subcategory

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  core-subcategory-Category : Subcategory lzero l2 C
  core-subcategory-Category =
    core-subprecategory-Precategory (precategory-Category C)

  is-wide-core-Category : is-wide-Subcategory C core-subcategory-Category
  is-wide-core-Category = is-wide-core-Precategory (precategory-Category C)
```

### The core precategory

```agda
core-precategory-Category :
  {l1 l2 : Level} (C : Category l1 l2) → Precategory l1 l2
core-precategory-Category C =
  core-precategory-Precategory (precategory-Category C)
```

### The core category

```agda
core-category-Category :
  {l1 l2 : Level} (C : Category l1 l2) → Category l1 l2
pr1 (core-category-Category C) = core-precategory-Category C
pr2 (core-category-Category C) =
  is-category-core-is-category-Precategory
    ( precategory-Category C)
    ( is-category-Category C)
```

### The core pregroupoid

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-pregroupoid-core-Category :
    is-pregroupoid-Precategory (core-precategory-Category C)
  is-pregroupoid-core-Category =
    is-pregroupoid-core-Precategory (precategory-Category C)

  core-pregroupoid-Category : Pregroupoid l1 l2
  core-pregroupoid-Category =
    core-pregroupoid-Precategory (precategory-Category C)
```

### The core groupoid

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  is-groupoid-core-Category : is-groupoid-Category (core-category-Category C)
  is-groupoid-core-Category = is-pregroupoid-core-Category C

  core-groupoid-Category : Groupoid l1 l2
  pr1 core-groupoid-Category = core-category-Category C
  pr2 core-groupoid-Category = is-groupoid-core-Category
```

## Properties

### Computing isomorphisms in the core

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) {x y : obj-Category C}
  where

  compute-iso-core-Category :
    iso-Category C x y ≃ iso-Category (core-category-Category C) x y
  compute-iso-core-Category =
    compute-iso-core-Precategory (precategory-Category C)

  inv-compute-iso-core-Category :
    iso-Category (core-category-Category C) x y ≃ iso-Category C x y
  inv-compute-iso-core-Category =
    inv-compute-iso-core-Precategory (precategory-Category C)
```

## See also

- [Cores of monoids](group-theory.cores-monoids.md)
- [Restrictions of functors to cores of precategories](category-theory.restrictions-functors-cores-precategories.md)

## External links

- [The core of a category](https://1lab.dev/Cat.Instances.Core.html) at 1lab
- [core groupoid](https://ncatlab.org/nlab/show/core+groupoid) at $n$Lab

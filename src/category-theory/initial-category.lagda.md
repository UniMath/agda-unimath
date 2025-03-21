# The initial category

```agda
module category-theory.initial-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-precategories
open import category-theory.gaunt-categories
open import category-theory.indiscrete-precategories
open import category-theory.precategories
open import category-theory.strict-categories
open import category-theory.strongly-preunivalent-categories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The **initial category** is the [category](category-theory.categories.md) with
no objects.

## Definition

### The objects and hom-sets of the initial category

```agda
obj-initial-Category : UU lzero
obj-initial-Category = empty

hom-set-initial-Category :
  obj-initial-Category → obj-initial-Category → Set lzero
hom-set-initial-Category _ _ = unit-Set

hom-initial-Category :
  obj-initial-Category → obj-initial-Category → UU lzero
hom-initial-Category x y = type-Set (hom-set-initial-Category x y)
```

### The underlying precategory of the initial category

```agda
comp-hom-initial-Category :
  {x y z : obj-initial-Category} →
  hom-initial-Category y z → hom-initial-Category x y → hom-initial-Category x z
comp-hom-initial-Category {x} {y} {z} =
  comp-hom-indiscrete-Precategory empty {x} {y} {z}

associative-comp-hom-initial-Category :
  {x y z w : obj-initial-Category}
  (h : hom-initial-Category z w)
  (g : hom-initial-Category y z)
  (f : hom-initial-Category x y) →
  comp-hom-initial-Category {x} {y} {w}
    ( comp-hom-initial-Category {y} {z} {w} h g)
    ( f) ＝
  comp-hom-initial-Category {x} {z} {w}
    ( h)
    ( comp-hom-initial-Category {x} {y} {z} g f)
associative-comp-hom-initial-Category {x} {y} {z} {w} =
  associative-comp-hom-indiscrete-Precategory empty {x} {y} {z} {w}

id-hom-initial-Category : {x : obj-initial-Category} → hom-initial-Category x x
id-hom-initial-Category {x} = id-hom-indiscrete-Precategory empty {x}

left-unit-law-comp-hom-initial-Category :
  {x y : obj-initial-Category}
  (f : hom-initial-Category x y) →
  comp-hom-initial-Category {x} {y} {y} (id-hom-initial-Category {y}) f ＝ f
left-unit-law-comp-hom-initial-Category {x} {y} =
  left-unit-law-comp-hom-indiscrete-Precategory empty {x} {y}

right-unit-law-comp-hom-initial-Category :
  {x y : obj-initial-Category}
  (f : hom-initial-Category x y) →
  comp-hom-initial-Category {x} {x} {y} f (id-hom-initial-Category {x}) ＝ f
right-unit-law-comp-hom-initial-Category {x} {y} =
  right-unit-law-comp-hom-indiscrete-Precategory empty {x} {y}

initial-Precategory : Precategory lzero lzero
initial-Precategory = indiscrete-Precategory empty
```

### The initial category

```agda
is-category-initial-Category :
  is-category-Precategory initial-Precategory
is-category-initial-Category ()

initial-Category : Category lzero lzero
pr1 initial-Category = initial-Precategory
pr2 initial-Category = is-category-initial-Category
```

### The initial strongly preunivalent category

```agda
is-strongly-preunivalent-initial-Category :
  is-strongly-preunivalent-Precategory initial-Precategory
is-strongly-preunivalent-initial-Category ()

-- initial-Preunivalent-Category : Preunivalent-Category lzero lzero
-- initial-Preunivalent-Category =
--   strongly-preunivalent-category-Category initial-Category
```

### The initial strict category

```agda
is-strict-category-initial-Category :
  is-strict-category-Precategory initial-Precategory
is-strict-category-initial-Category ()

initial-Strict-Category : Strict-Category lzero lzero
pr1 initial-Strict-Category = initial-Precategory
pr2 initial-Strict-Category = is-strict-category-initial-Category
```

### The initial gaunt category

```agda
is-gaunt-initial-Category : is-gaunt-Category initial-Category
is-gaunt-initial-Category ()

initial-Gaunt-Category : Gaunt-Category lzero lzero
pr1 initial-Gaunt-Category = initial-Category
pr2 initial-Gaunt-Category = is-gaunt-initial-Category
```

## Properties

### The initial category is initial

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  initial-functor-Precategory : functor-Precategory initial-Precategory C
  pr1 initial-functor-Precategory ()
  pr1 (pr2 initial-functor-Precategory) {()}
  pr1 (pr2 (pr2 initial-functor-Precategory)) {()}
  pr2 (pr2 (pr2 initial-functor-Precategory)) ()

  abstract
    uniqueness-initial-functor-Precategory :
      (F : functor-Precategory initial-Precategory C) →
      initial-functor-Precategory ＝ F
    uniqueness-initial-functor-Precategory F =
      eq-htpy-functor-Precategory
        ( initial-Precategory)
        ( C)
        ( initial-functor-Precategory)
        ( F)
        ( (λ where ()) , (λ where {()}))

  abstract
    is-contr-functor-initial-Precategory :
      is-contr (functor-Precategory initial-Precategory C)
    pr1 is-contr-functor-initial-Precategory =
      initial-functor-Precategory
    pr2 is-contr-functor-initial-Precategory =
      uniqueness-initial-functor-Precategory
```

## See also

- [The terminal category](category-theory.terminal-category.md)

## External links

- [empty category](https://ncatlab.org/nlab/show/empty+category) at $n$Lab

A wikidata identifier was not available for this concept.

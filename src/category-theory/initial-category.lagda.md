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
open import category-theory.preunivalent-categories
open import category-theory.strict-categories

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
comp-hom-initial-Category =
  comp-hom-indiscrete-Precategory empty

associative-comp-hom-initial-Category =
  associative-comp-hom-indiscrete-Precategory empty

associative-composition-operation-initial-Category =
  associative-composition-operation-indiscrete-Precategory empty

id-hom-initial-Category = id-hom-indiscrete-Precategory empty

left-unit-law-comp-hom-initial-Category =
  left-unit-law-comp-hom-indiscrete-Precategory empty

right-unit-law-comp-hom-initial-Category =
  right-unit-law-comp-hom-indiscrete-Precategory empty

is-unital-composition-operation-initial-Category =
  is-unital-composition-operation-indiscrete-Precategory empty

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

### The initial preunivalent category

```agda
is-preunivalent-initial-Category :
  is-preunivalent-Precategory initial-Precategory
is-preunivalent-initial-Category ()

initial-Preunivalent-Category : Preunivalent-Category lzero lzero
initial-Preunivalent-Category =
  preunivalent-category-Category initial-Category
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

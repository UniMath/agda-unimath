# Endomorphisms in categories

```agda
module category-theory.endomorphisms-in-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.endomorphisms-in-precategories

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Definition

### The monoid of endomorphisms on an object in a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) (X : obj-Category C)
  where

  type-endo-Category : UU l2
  type-endo-Category = type-endo-Precategory (precategory-Category C) X

  comp-endo-Category :
    type-endo-Category → type-endo-Category → type-endo-Category
  comp-endo-Category = comp-endo-Precategory (precategory-Category C) X

  id-endo-Category : type-endo-Category
  id-endo-Category = id-endo-Precategory (precategory-Category C) X

  associative-comp-endo-Category :
    (h g f : type-endo-Category) →
    ( comp-endo-Category (comp-endo-Category h g) f) ＝
    ( comp-endo-Category h (comp-endo-Category g f))
  associative-comp-endo-Category =
    associative-comp-endo-Precategory (precategory-Category C) X

  left-unit-law-comp-endo-Category :
    (f : type-endo-Category) → comp-endo-Category id-endo-Category f ＝ f
  left-unit-law-comp-endo-Category =
    left-unit-law-comp-endo-Precategory (precategory-Category C) X

  right-unit-law-comp-endo-Category :
    (f : type-endo-Category) → comp-endo-Category f id-endo-Category ＝ f
  right-unit-law-comp-endo-Category =
    right-unit-law-comp-endo-Precategory (precategory-Category C) X

  set-endo-Category : Set l2
  set-endo-Category = set-endo-Precategory (precategory-Category C) X

  semigroup-endo-Category : Semigroup l2
  semigroup-endo-Category =
    semigroup-endo-Precategory (precategory-Category C) X

  monoid-endo-Category : Monoid l2
  monoid-endo-Category = monoid-endo-Precategory (precategory-Category C) X
```

# Endomorphisms of objects in categories

```agda
module category-theory.endomorphisms-of-objects-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories

open import foundation.dependent-pair-types
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

  endo-Category : UU l2
  endo-Category = type-hom-Category C X X

  comp-endo-Category : endo-Category → endo-Category → endo-Category
  comp-endo-Category g f = comp-hom-Category C g f

  id-endo-Category : endo-Category
  id-endo-Category = id-hom-Category C

  associative-comp-endo-Category :
    (h g f : endo-Category) →
    ( comp-endo-Category (comp-endo-Category h g) f) ＝
    ( comp-endo-Category h (comp-endo-Category g f))
  associative-comp-endo-Category = associative-comp-hom-Category C

  left-unit-law-comp-endo-Category :
    (f : endo-Category) → comp-endo-Category id-endo-Category f ＝ f
  left-unit-law-comp-endo-Category = left-unit-law-comp-hom-Category C

  right-unit-law-comp-endo-Category :
    (f : endo-Category) → comp-endo-Category f id-endo-Category ＝ f
  right-unit-law-comp-endo-Category = right-unit-law-comp-hom-Category C

  set-endo-Category : Set l2
  set-endo-Category = hom-Category C X X

  semigroup-endo-Category : Semigroup l2
  pr1 semigroup-endo-Category = set-endo-Category
  pr1 (pr2 semigroup-endo-Category) = comp-endo-Category
  pr2 (pr2 semigroup-endo-Category) = associative-comp-endo-Category

  monoid-endo-Category : Monoid l2
  pr1 monoid-endo-Category = semigroup-endo-Category
  pr1 (pr2 monoid-endo-Category) = id-endo-Category
  pr1 (pr2 (pr2 monoid-endo-Category)) = left-unit-law-comp-endo-Category
  pr2 (pr2 (pr2 monoid-endo-Category)) = right-unit-law-comp-endo-Category
```

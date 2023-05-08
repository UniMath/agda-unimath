# Functors between categories

```agda
module category-theory.functors-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A functor between two categories is a functor between the underlying
precategories.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  where

  functor-Category : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Category =
    functor-Precategory (precategory-Category C) (precategory-Category D)

  obj-functor-Category : functor-Category → obj-Category C → obj-Category D
  obj-functor-Category = pr1

  hom-functor-Category :
    (F : functor-Category) →
    {x y : obj-Category C} →
    (f : type-hom-Category C x y) →
    type-hom-Category D (obj-functor-Category F x) (obj-functor-Category F y)
  hom-functor-Category F = pr1 (pr2 F)

  preserves-comp-functor-Category :
    ( F : functor-Category) {x y z : obj-Category C}
    ( g : type-hom-Category C y z) (f : type-hom-Category C x y) →
    ( hom-functor-Category F (comp-hom-Category C g f)) ＝
    ( comp-hom-Category D (hom-functor-Category F g) (hom-functor-Category F f))
  preserves-comp-functor-Category F =
    preserves-comp-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D) F

  preserves-id-functor-Category :
    (F : functor-Category) (x : obj-Category C) →
    hom-functor-Category F (id-hom-Category C {x}) ＝
    id-hom-Category D {obj-functor-Category F x}
  preserves-id-functor-Category F =
    preserves-id-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D) F
```

## Examples

### The identity functor

There is an identity functor on any category.

```agda
id-functor-Category :
  {l1 l2 : Level} (C : Category l1 l2) → functor-Category C C
id-functor-Category C = id-functor-Precategory (precategory-Category C)
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
comp-functor-Category :
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Category l1 l2) (D : Category l3 l4) (E : Category l5 l6) →
  functor-Category D E → functor-Category C D → functor-Category C E
comp-functor-Category C D E G F =
  comp-functor-Precategory
    ( precategory-Category C)
    ( precategory-Category D)
    ( precategory-Category E)
    ( G)
    ( F)
```

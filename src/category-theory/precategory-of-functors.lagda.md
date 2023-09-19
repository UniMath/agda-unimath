# The precategory of functors and natural transformations between two fixed precategories

```agda
module category-theory.precategory-of-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) and
[natural transformations](category-theory.natural-transformations-precategories.md)
between them introduce a new precategory whose identity map and composition
structure are inherited pointwise from the codomain precategory. This is called
the **precategory of functors**.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  comp-hom-functor-precategory-Precategory :
    {F G H : functor-Precategory C D} →
    natural-transformation-Precategory C D G H →
    natural-transformation-Precategory C D F G →
    natural-transformation-Precategory C D F H
  comp-hom-functor-precategory-Precategory {F} {G} {H} =
    comp-natural-transformation-Precategory C D F G H

  associative-comp-hom-functor-precategory-Precategory :
    {F G H I : functor-Precategory C D}
    (h : natural-transformation-Precategory C D H I)
    (g : natural-transformation-Precategory C D G H)
    (f : natural-transformation-Precategory C D F G) →
    (comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I h g)
      ( f)) ＝
    ( comp-natural-transformation-Precategory C D F H I
      ( h)
      ( comp-natural-transformation-Precategory C D F G H g f))
  associative-comp-hom-functor-precategory-Precategory {F} {G} {H} {I} h g f =
    associative-comp-natural-transformation-Precategory
      C D {F} {G} {H} {I} f g h

  associative-composition-structure-functor-precategory-Precategory :
    associative-composition-structure-Set
      ( natural-transformation-Precategory-Set C D)
  pr1 associative-composition-structure-functor-precategory-Precategory
    {F} {G} {H} =
    comp-hom-functor-precategory-Precategory {F} {G} {H}
  pr2 associative-composition-structure-functor-precategory-Precategory
    {F} {G} {H} {I} =
    associative-comp-hom-functor-precategory-Precategory {F} {G} {H} {I}

  id-hom-functor-precategory-Precategory :
    (F : functor-Precategory C D) → natural-transformation-Precategory C D F F
  id-hom-functor-precategory-Precategory =
    id-natural-transformation-Precategory C D

  left-unit-law-comp-hom-functor-precategory-Precategory :
    {F G : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G) →
    ( comp-natural-transformation-Precategory C D F G G
      ( id-natural-transformation-Precategory C D G) α) ＝
    ( α)
  left-unit-law-comp-hom-functor-precategory-Precategory {F} {G} =
    left-unit-law-comp-natural-transformation-Precategory C D {F} {G}

  right-unit-law-comp-hom-functor-precategory-Precategory :
    {F G : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G) →
    ( comp-natural-transformation-Precategory C D F F G
        α (id-natural-transformation-Precategory C D F)) ＝
    ( α)
  right-unit-law-comp-hom-functor-precategory-Precategory {F} {G} =
    right-unit-law-comp-natural-transformation-Precategory C D {F} {G}

  is-unital-composition-structure-functor-precategory-Precategory :
    is-unital-composition-structure-Set
      ( natural-transformation-Precategory-Set C D)
      ( associative-composition-structure-functor-precategory-Precategory)
  pr1 is-unital-composition-structure-functor-precategory-Precategory =
    id-hom-functor-precategory-Precategory
  pr1
    ( pr2 is-unital-composition-structure-functor-precategory-Precategory)
    { F} {G} =
    left-unit-law-comp-hom-functor-precategory-Precategory {F} {G}
  pr2
    ( pr2 is-unital-composition-structure-functor-precategory-Precategory)
    { F} {G} =
    right-unit-law-comp-hom-functor-precategory-Precategory {F} {G}

  functor-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 functor-precategory-Precategory = functor-Precategory C D
  pr1 (pr2 functor-precategory-Precategory) =
    natural-transformation-Precategory-Set C D
  pr1 (pr2 (pr2 functor-precategory-Precategory)) =
    associative-composition-structure-functor-precategory-Precategory
  pr2 (pr2 (pr2 functor-precategory-Precategory)) =
    is-unital-composition-structure-functor-precategory-Precategory
```

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
open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) and
[natural transformations](category-theory.natural-transformations-precategories.md)
between them introduce a new precategory whose identity map and composition
structure are inherited pointwise from the codomain precategory.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  functor-precategory-Precategory :
    Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 functor-precategory-Precategory = functor-Precategory C D
  pr1 (pr2 functor-precategory-Precategory) F G =
    natural-transformation-Precategory-Set C D F G
  pr1 (pr2 (pr2 functor-precategory-Precategory)) =
    ( λ {F} {G} {H} → comp-natural-transformation-Precategory C D F G H) ,
    ( λ {F} {G} {H} {I} h g f →
      associative-comp-natural-transformation-Precategory
        C D {F} {G} {H} {I} f g h)
  pr2 (pr2 (pr2 functor-precategory-Precategory)) =
    (id-natural-transformation-Precategory C D) ,
    ( λ {F} {G} →
      left-unit-law-comp-natural-transformation-Precategory C D {F} {G}) ,
    ( λ {F} {G} →
      right-unit-law-comp-natural-transformation-Precategory C D {F} {G})
```

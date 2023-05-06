# Natural transformations between functors between categories

```agda
module category-theory.natural-transformations-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.natural-transformations-precategories

open import foundation.universe-levels
```

</details>

## Idea

A natural transformation between functors on categories is a natural
transformation between the functors on the underlying precategories.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : functor-Category C D)
  where

  is-natural-transformation-Category :
    ( ( x : obj-Category C) →
      type-hom-Category D
        ( obj-functor-Category C D F x)
        ( obj-functor-Category C D G x)) →
    UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-Category =
    is-natural-transformation-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  natural-transformation-Category : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-Category =
    natural-transformation-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  components-natural-transformation-Category :
    natural-transformation-Category → (x : obj-Category C) →
    type-hom-Category D
      ( obj-functor-Category C D F x)
      ( obj-functor-Category C D G x)
  components-natural-transformation-Category =
    components-natural-transformation-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

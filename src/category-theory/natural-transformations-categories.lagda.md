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
  (C : Cat l1 l2)
  (D : Cat l3 l4)
  (F G : functor-Cat C D)
  where

  is-natural-transformation-Cat :
    ( (x : obj-Cat C) →
      type-hom-Cat D (obj-functor-Cat C D F x) (obj-functor-Cat C D G x)) →
    UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-Cat =
    is-natural-transformation-Precategory
      ( precategory-Cat C)
      ( precategory-Cat D)
      ( F)
      ( G)

  natural-transformation-Cat : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-Cat =
    natural-transformation-Precategory
      ( precategory-Cat C)
      ( precategory-Cat D)
      ( F)
      ( G)

  components-natural-transformation-Cat :
    natural-transformation-Cat → (x : obj-Cat C) →
    type-hom-Cat D (obj-functor-Cat C D F x) (obj-functor-Cat C D G x)
  components-natural-transformation-Cat =
    components-natural-transformation-Precategory
      ( precategory-Cat C)
      ( precategory-Cat D)
      ( F)
      ( G)
```

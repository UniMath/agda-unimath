# Natural isomorphisms between functors between categories

```agda
module category-theory.natural-isomorphisms-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.natural-isomorphisms-precategories
open import category-theory.natural-transformations-categories

open import foundation.universe-levels
```

</details>

## Idea

A natural isomorphism between functors on categories is a natural isomorphism
between the functors on the underlying precategories.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : functor-Category C D)
  where

  is-natural-isomorphism-Category :
    natural-transformation-Category C D F G → UU (l1 ⊔ l4)
  is-natural-isomorphism-Category =
    is-natural-isomorphism-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  natural-isomorphism-Category : UU (l1 ⊔ l2 ⊔ l4)
  natural-isomorphism-Category =
    natural-isomorphism-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

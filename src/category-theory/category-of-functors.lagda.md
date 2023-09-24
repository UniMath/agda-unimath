# The category of functors and natural transformations between two categories

```agda
module category-theory.category-of-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.precategories
open import category-theory.precategory-of-functors

open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-categories.md) between
[categories](category-theory.categories.md) and
[natural transformations](category-theory.natural-transformations-categories.md)
between them introduce a new category whose identity map and composition
structure are inherited pointwise from the codomain category. This is called the
**category of functors**.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Category l1 l2) (D : Category l3 l4)
  where

  precategory-functor-category-Category :
    Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  precategory-functor-category-Category =
    functor-precategory-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  -- is-category-precategory-functor-category-Category :
  --   is-category-Precategory precategory-functor-category-Category
  -- is-category-precategory-functor-category-Category F G =
  --   is-equiv-htpy-equiv
  --     ( equiv-iso-functor-natural-isomorphism-Precategory
  --       ( precategory-Category C)
  --       ( precategory-Category D)
  --       ( F)
  --       ( G) ∘e
  --       {!  !} ∘e
  --       equiv-Σ-equiv-base _
  --         ( equiv-Π-equiv-family
  --           ( λ i → extensionality-obj-Category D
  --             ( obj-functor-Category C D F i)
  --             ( obj-functor-Category C D G i))) ∘e
  --       ( equiv-htpy-map-eq-functor-Category C D F G))
  --     {!   !}

  -- functor-category-Category :
  --   Category (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  -- pr1 functor-category-Category = precategory-functor-category-Category
  -- pr2 functor-category-Category = is-category-precategory-functor-category-Category
```

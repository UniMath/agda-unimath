# The category of functors and natural transformations between two fixed categories

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

  functor-category-Precategory : Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  functor-category-Precategory =
    functor-precategory-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  -- is-category-functor-category-Precategory :
  --   is-category-Precategory functor-category-Precategory
  -- is-category-functor-category-Precategory F G =
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
  --       ( extensionality-functor-Category C D F G))
  --     {!   !}

  -- functor-category-Category :
  --   Category (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  -- pr1 functor-category-Category = functor-category-Precategory
  -- pr2 functor-category-Category = is-category-functor-category-Precategory
```

# Large subcategories

```agda
module category-theory.large-subcategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-categories
open import category-theory.large-categories
open import category-theory.large-subprecategories

open import foundation.universe-levels
```

</details>

## Idea

A **large subcategory** of a [large category](category-theory.large-categories.md) `C` is a [large subprecategory](category-theory.large-subprecategories.md) `P` of the underlying [large precategory](category-theory.large-precategories.md) of `C` which is in addition assumed to be closed under [isomorphisms](category-theory.isomorphisms-in-large-categories.md).

We add this extra assumption of being closed under isomorphisms to generalize the situation for subcategories of small [categories](category-theory.categories.md), which are automatically closed under [isomorphisms](category-theory.isomorphisms-in-categories.md). In the case of large categories, however, this is an extra assumption because there may be isomorphisms between objects of different universe levels.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (γ : Level → Level) (δ : Level → Level → Level)
  (C : Large-Category α β)
  where

  record
    Large-Subcategory : UUω
    where
    field
      large-subprecategory-Large-Subcategory :
        Large-Subprecategory γ δ (large-precategory-Large-Category C)
      is-closed-under-isomorphisms-Large-Subcategory :
        {l1 l2 : Level}
        (X : obj-Large-Category C l1) (Y : obj-Large-Category C l2) →
        iso-Large-Category C X Y →
        is-in-subtype-obj-Large-Subprecategory
          ( large-precategory-Large-Category C)
          ( large-subprecategory-Large-Subcategory)
          ( X) → 
        is-in-subtype-obj-Large-Subprecategory
          ( large-precategory-Large-Category C)
          ( large-subprecategory-Large-Subcategory)
          ( Y) 
```

# The category of group actions

```agda
module group-theory.category-of-group-actions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
open import group-theory.isomorphisms-group-actions
open import group-theory.precategory-of-group-actions
```

</details>

## Idea

The [large category](category-theory.large-categories.md) of
[group actions](group-theory.group-actions.md) consists of group actions and
[morphisms of group actions](group-theory.homomorphisms-group-actions.md)
between them.

## Definitions

### The large category of `G`-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-large-category-action-Group-Large-Category :
    is-large-category-Large-Precategory (action-Group-Large-Precategory G)
  is-large-category-action-Group-Large-Category X =
    fundamental-theorem-id
      ( is-torsorial-iso-action-Group G X)
      ( iso-eq-Large-Precategory (action-Group-Large-Precategory G) X)

  action-Group-Large-Category :
    Large-Category (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-precategory-Large-Category action-Group-Large-Category =
      action-Group-Large-Precategory G
  is-large-category-Large-Category action-Group-Large-Category =
    is-large-category-action-Group-Large-Category
```

### The small category of `G`-sets

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  action-Group-Category :
    (l2 : Level) → Category (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  action-Group-Category =
    category-Large-Category (action-Group-Large-Category G)
```

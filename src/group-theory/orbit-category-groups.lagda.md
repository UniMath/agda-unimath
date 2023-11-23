# The orbit category of a group

```agda
module group-theory.orbit-category-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.full-large-subcategories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import group-theory.category-of-group-actions
open import group-theory.group-actions
open import group-theory.groups
open import group-theory.homomorphisms-group-actions
open import group-theory.isomorphisms-group-actions
open import group-theory.precategory-of-group-actions
open import group-theory.transitive-group-actions
```

</details>

## Idea

The **orbit category of a group** `Orb(G)` is the
[full subcategory](category-theory.full-large-subcategories.md) of the
[category of `G`-sets](group-theory.category-of-group-actions.md) consisting of
_homogenous_ `G`-sets, i.e. `G`-sets whose
[`G`-action](group-theory.group-actions.md) is
[transitive](group-theory.transitive-group-actions.md).

## Definitions

### The large orbit category of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  orbit-Group-Full-Large-Subcategory :
    Full-Large-Subcategory (l1 ⊔_) (action-Group-Large-Category G)
  orbit-Group-Full-Large-Subcategory = is-transitive-prop-action-Group G

  orbit-Group-Large-Category :
    Large-Category (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  orbit-Group-Large-Category =
    large-category-Full-Large-Subcategory
      ( action-Group-Large-Category G)
      ( orbit-Group-Full-Large-Subcategory)
```

### The large orbit precategory of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  orbit-Group-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  orbit-Group-Large-Precategory =
    large-precategory-Large-Category (orbit-Group-Large-Category G)
```

### The small orbit category of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  orbit-Group-Category : (l2 : Level) → Category (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  orbit-Group-Category = category-Large-Category (orbit-Group-Large-Category G)
```

### The small orbit precategory of a group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  orbit-Group-Precategory : (l2 : Level) → Precategory (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  orbit-Group-Precategory =
    precategory-Large-Category (orbit-Group-Large-Category G)
```

## External links

- [orbit category](https://ncatlab.org/nlab/show/orbit+category) at $n$Lab

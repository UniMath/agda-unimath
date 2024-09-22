# The category of metric spaces and isometries

```agda
module metric-spaces.category-of-metric-spaces-and-isometries where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories

open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import metric-spaces.precategory-of-metric-spaces-and-isometries
```

</details>

## Idea

The
[precategory of metric spaces and isometries](metric-spaces.precategory-of-metric-spaces-and-isometries.md)
is a [category](category-theory.categories.md).

## Definitions

### The precategory of metric spaces and isometries is a category

```agda
module _
  {l1 l2 : Level}
  where

  is-category-precategory-isometry-Metric-Space :
    is-category-Precategory (precategory-isometry-Metric-Space {l1} {l2})
  is-category-precategory-isometry-Metric-Space A =
    fundamental-theorem-id
      ( is-torsorial-iso-precategory-isometry-Metric-Space A)
      ( iso-eq-Precategory precategory-isometry-Metric-Space A)
```

### The category of metric spaces and isometries

```agda
module _
  {l1 l2 : Level}
  where

  category-isometry-Metric-Space : Category (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 category-isometry-Metric-Space =
    precategory-isometry-Metric-Space {l1} {l2}
  pr2 category-isometry-Metric-Space =
    is-category-precategory-isometry-Metric-Space
```

# The category of metric spaces and short maps

```agda
module metric-spaces.category-of-metric-spaces-and-short-functions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import metric-spaces.precategory-of-metric-spaces-and-short-functions
```

</details>

## Idea

The
[precategory of metric spaces and short maps](metric-spaces.precategory-of-metric-spaces-and-short-functions.md)
is a [category](category-theory.categories.md).

## Definition

```agda
module _
  {l : Level}
  where

  category-short-function-Metric-Space : Category (lsuc l) l
  pr1 category-short-function-Metric-Space =
    precategory-short-function-Metric-Space
  pr2 category-short-function-Metric-Space A =
    fundamental-theorem-id
      ( is-torsorial-iso-precategory-short-function-Metric-Space A)
      ( iso-eq-Precategory precategory-short-function-Metric-Space A)
```

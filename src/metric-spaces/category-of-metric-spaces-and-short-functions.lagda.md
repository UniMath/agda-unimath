# The category of metric spaces and short maps

```agda
module metric-spaces.category-of-metric-spaces-and-short-functions where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-short-functions
```

</details>

## Idea

The
[precategory of metric spaces and short maps](metric-spaces.precategory-of-metric-spaces-and-short-functions.md)
is a [category](category-theory.categories.md). We call this the
{{#concept "category of metric spaces and short maps" Agda=category-short-function-Metric-Space WD="category of metric spaces" WDID=Q5051850}}.

## Definitions

### The precategory of metric spaces and short maps is a category

```agda
module _
  {l1 l2 : Level}
  where

  is-torsorial-iso-short-function-Metric-Space :
    (A : Metric-Space l1 l2) →
    is-torsorial (iso-Precategory precategory-short-function-Metric-Space A)
  is-torsorial-iso-short-function-Metric-Space A =
    is-contr-equiv
      ( Σ (Metric-Space l1 l2) (isometric-equiv-Metric-Space' A))
      ( equiv-tot
        ( equiv-isometric-equiv-iso-short-function-Metric-Space'
          ( A)))
      ( is-torsorial-isometric-equiv-Metric-Space' A)

  is-category-precategory-short-function-Metric-Space :
    is-category-Precategory (precategory-short-function-Metric-Space {l1} {l2})
  is-category-precategory-short-function-Metric-Space A =
    fundamental-theorem-id
      ( is-torsorial-iso-short-function-Metric-Space A)
      ( iso-eq-Precategory precategory-short-function-Metric-Space A)
```

### The category of metric spaces and short maps

```agda
module _
  {l1 l2 : Level}
  where

  category-short-function-Metric-Space : Category (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 category-short-function-Metric-Space =
    precategory-short-function-Metric-Space {l1} {l2}
  pr2 category-short-function-Metric-Space =
    is-category-precategory-short-function-Metric-Space
```

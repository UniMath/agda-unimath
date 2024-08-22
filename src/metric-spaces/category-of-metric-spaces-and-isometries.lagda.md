# The category of metric spaces and isometries

```agda
module metric-spaces.category-of-metric-spaces-and-isometries where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-isometries
```

</details>

## Idea

The
[precatogory of metric spaces and isometries](metric-spaces.precategory-of-metric-spaces-and-isometries.md)
is a [category](category-theory.categories.md).

## Definition

```agda
module _
  {l : Level}
  where

  category-isometry-Metric-Space : Category (lsuc l) l
  pr1 category-isometry-Metric-Space = precategory-isometry-Metric-Space
  pr2 category-isometry-Metric-Space A =
    fundamental-theorem-id
      ( is-torsorial-iso-precategory-isometry-Metric-Space A)
      ( iso-eq-Precategory precategory-isometry-Metric-Space A)
```

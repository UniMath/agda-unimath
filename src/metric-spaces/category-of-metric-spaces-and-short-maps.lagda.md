# The category of metric spaces and short maps

```agda
module metric-spaces.category-of-metric-spaces-and-short-maps where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-short-maps
```

</details>

## Idea

The
[precategory of metric spaces and short maps](metric-spaces.precategory-of-metric-spaces-and-short-maps.md)
is a [category](category-theory.categories.md). We call this the
{{#concept "category of metric spaces and short maps" Agda=category-short-map-Metric-Space WD="category of metric spaces" WDID=Q5051850}}.

## Definitions

### The precategory of metric spaces and short maps is a category

```agda
module _
  {l1 l2 : Level}
  where

  is-torsorial-iso-short-map-Metric-Space :
    (A : Metric-Space l1 l2) →
    is-torsorial (iso-Precategory precategory-short-map-Metric-Space A)
  is-torsorial-iso-short-map-Metric-Space A =
    is-contr-equiv
      ( Σ (Metric-Space l1 l2) (isometric-equiv-Metric-Space' A))
      ( equiv-tot
        ( equiv-isometric-equiv-iso-short-map-Metric-Space'
          ( A)))
      ( is-torsorial-isometric-equiv-Metric-Space' A)

  is-category-precategory-short-map-Metric-Space :
    is-category-Precategory (precategory-short-map-Metric-Space {l1} {l2})
  is-category-precategory-short-map-Metric-Space A =
    fundamental-theorem-id
      ( is-torsorial-iso-short-map-Metric-Space A)
      ( iso-eq-Precategory precategory-short-map-Metric-Space A)
```

### The category of metric spaces and short maps

```agda
module _
  {l1 l2 : Level}
  where

  category-short-map-Metric-Space : Category (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 category-short-map-Metric-Space =
    precategory-short-map-Metric-Space {l1} {l2}
  pr2 category-short-map-Metric-Space =
    is-category-precategory-short-map-Metric-Space
```

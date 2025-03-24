# The category of metric spaces and isometries

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module metric-spaces.category-of-metric-spaces-and-isometries
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.isomorphisms-in-precategories funext univalence truncations

open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces funext univalence truncations
open import metric-spaces.metric-spaces funext univalence truncations
open import metric-spaces.precategory-of-metric-spaces-and-isometries funext univalence truncations
```

</details>

## Idea

The
[precategory of metric spaces and isometries](metric-spaces.precategory-of-metric-spaces-and-isometries.md)
is a [category](category-theory.categories.md). We call this the
{{#concept "category of metric spaces and isometries" Agda=category-isometry-Metric-Space}}.

## Definitions

### The precategory of metric spaces and isometries is a category

```agda
module _
  {l1 l2 : Level}
  where

  is-torsorial-iso-isometry-Metric-Space :
    (A : Metric-Space l1 l2) →
    is-torsorial (iso-Precategory precategory-isometry-Metric-Space A)
  is-torsorial-iso-isometry-Metric-Space A =
    is-contr-equiv
      ( Σ (Metric-Space l1 l2) (isometric-equiv-Metric-Space' A))
      ( equiv-tot (equiv-iso-isometric-equiv-Metric-Space' A))
      ( is-torsorial-isometric-equiv-Metric-Space' A)

  is-category-precategory-isometry-Metric-Space :
    is-category-Precategory (precategory-isometry-Metric-Space {l1} {l2})
  is-category-precategory-isometry-Metric-Space A =
    fundamental-theorem-id
      ( is-torsorial-iso-isometry-Metric-Space A)
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

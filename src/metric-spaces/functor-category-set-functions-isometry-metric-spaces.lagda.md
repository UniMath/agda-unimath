# The functor from the precategory of metric spaces and isometries to the precategory of sets

```agda
module metric-spaces.functor-category-set-functions-isometry-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import category-theory.conservative-functors-precategories
open import category-theory.faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.category-of-sets
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isomorphisms-of-sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.category-of-metric-spaces-and-isometries
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-isometries
```

</details>

## Idea

Because carrier types of [metric spaces](metric-spaces.metric-spaces.md) are
[sets](foundation.sets.md), there's a forgetful
[functor](category-theory.functors-precategories.md) from the
[category of metric spaces and isometries](metric-spaces.category-of-metric-spaces-and-isometries.md)
to the [category of sets](foundation.category-of-sets.md). Moreover, since the
map from an isometry to its carrier map is an
[embedding](foundation.embeddings.md), this functor is
[faithful](category-theory.faithful-functors-precategories.md). Finally, because
the inverse of an isometric equivalence is an isometry, this functor is also
[conservative](category-theory.conservative-functors-precategories.md).

## Definition

### The forgetful functor from metric spaces and isometries to sets and functions

```agda
module _
  (l1 l2 : Level)
  where

  functor-set-functions-isometry-Metric-Space :
    functor-Precategory
      ( precategory-isometry-Metric-Space {l1} {l2})
      ( Set-Precategory l1)
  pr1 functor-set-functions-isometry-Metric-Space A =
      set-Metric-Space A
  pr2 functor-set-functions-isometry-Metric-Space =
    ( λ {A B} → map-isometry-Metric-Space A B) ,
    ( ( λ g f → refl) , ( λ A → refl))
```

## Properties

### The functor from metric spaces and isometries to sets and functions is faithful

```agda
module _
  (l1 l2 : Level)
  where

  is-faithful-functor-set-functions-isometry-Metric-Space :
    is-faithful-functor-Precategory
      ( precategory-isometry-Metric-Space)
      ( Set-Precategory l1)
      ( functor-set-functions-isometry-Metric-Space l1 l2)
  is-faithful-functor-set-functions-isometry-Metric-Space A B =
    is-emb-inclusion-subtype (is-isometry-prop-Metric-Space A B)
```

### The functor from metric spaces and isometries to sets and functions is conservative

```agda
module _
  (l1 l2 : Level)
  where

  is-conservative-functor-set-functions-isometry-Metric-Space :
    is-conservative-functor-Precategory
      ( precategory-isometry-Metric-Space)
      ( Set-Precategory l1)
      ( functor-set-functions-isometry-Metric-Space l1 l2)
  is-conservative-functor-set-functions-isometry-Metric-Space
    {A} {B} f =
    ( is-iso-is-equiv-isometry-Metric-Space A B f) ∘
    ( is-equiv-is-iso-Set
      ( set-Metric-Space A)
      ( set-Metric-Space B))
```

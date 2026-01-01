# The inclusion of isometries into the category of metric spaces and short maps

```agda
module metric-spaces.functor-category-short-isometry-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import category-theory.conservative-functors-precategories
open import category-theory.faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.precategories
open import category-theory.split-essentially-surjective-functors-precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-isometries
open import metric-spaces.precategory-of-metric-spaces-and-short-maps
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

Because every [isometry](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is also
[short](metric-spaces.short-maps-metric-spaces.md), there's a
[functor](category-theory.functors-precategories.md) between the
[category of metric spaces and isometries](metric-spaces.category-of-metric-spaces-and-isometries.md)
to the
[category of metric spaces and short maps](metric-spaces.category-of-metric-spaces-and-short-maps.md).

Since this functor is the identity on objects, it is an equivalence on objects.
Moreover, since the map from isometry to short maps is an
[embedding](foundation.embeddings.md), this functor is
[faithful](category-theory.faithful-functors-precategories.md). Finally, because
short [isomorphisms](category-theory.isomorphisms-in-precategories.md) are
isometries, this functor is also
[conservative](category-theory.conservative-functors-precategories.md).

## Definition

### The functor between the category of metric spaces and isometries to the category of metric spaces and short maps

```agda
module _
  (l1 l2 : Level)
  where

  functor-short-map-isometry-Metric-Space :
    functor-Precategory
      (precategory-isometry-Metric-Space {l1} {l2})
      (precategory-short-map-Metric-Space {l1} {l2})
  pr1 functor-short-map-isometry-Metric-Space A = A
  pr2 functor-short-map-isometry-Metric-Space =
    ( λ {A B} → short-map-isometry-Metric-Space A B) ,
    ( ( λ g f → refl) , ( λ A → refl))
```

## Properties

### The functor from isometries to short maps is an equivalence on objects

```agda
module _
  (l1 l2 : Level)
  where

  is-equiv-obj-functor-short-map-isometry-Metric-Space :
    is-equiv
      ( obj-functor-Precategory
        ( precategory-isometry-Metric-Space)
        ( precategory-short-map-Metric-Space)
        ( functor-short-map-isometry-Metric-Space l1 l2))
  is-equiv-obj-functor-short-map-isometry-Metric-Space = is-equiv-id
```

### The functor from isometries to short maps is faithful

```agda
module _
  (l1 l2 : Level)
  where

  is-faithful-functor-short-map-isometry-Metric-Space :
    is-faithful-functor-Precategory
      (precategory-isometry-Metric-Space)
      (precategory-short-map-Metric-Space)
      (functor-short-map-isometry-Metric-Space l1 l2)
  is-faithful-functor-short-map-isometry-Metric-Space =
    is-emb-short-map-isometry-Metric-Space
```

### The functor from isometries to short maps is conservative

```agda
module _
  (l1 l2 : Level)
  where

  is-conservative-functor-short-map-isometry-Metric-Space :
    is-conservative-functor-Precategory
      (precategory-isometry-Metric-Space)
      (precategory-short-map-Metric-Space)
      (functor-short-map-isometry-Metric-Space l1 l2)
  is-conservative-functor-short-map-isometry-Metric-Space {A} {B} f H =
    is-iso-is-equiv-isometry-Metric-Space
      ( A)
      ( B)
      ( f)
      ( is-equiv-is-iso-short-map-Metric-Space
        ( A)
        ( B)
        ( short-map-isometry-Metric-Space A B f)
        ( H))
```

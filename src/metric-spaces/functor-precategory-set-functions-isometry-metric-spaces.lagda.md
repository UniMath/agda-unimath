# The functor from the precategory of metric spaces and isometries to the precategory of sets

```agda
module metric-spaces.functor-precategory-set-functions-isometry-metric-spaces where
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
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-isometries
```

</details>

## Idea

Because [metric spaces](metric-spaces.metric-spaces.md) is
[set](foundation.sets.md), there's a forgetful
[functor](category-theory.functor-precategories.md) from the
[precategory of metric spaces and isometries](metric-spaces.precategory-of-metric-spaces-and-isometries.md)
to the [precategory of sets](foundation.category-of-sets.md).

Moreover, since the map from an isometry to its carrier map is an
[embedding](foundation.embeddings.md), this functor is
[faithful](category-theory.faithful-functors-precategories.md).

Finally, because the inverse of an isometric equivalnce is isometric, this
functor is also
[conservative](category-theory.conservative-functors-precategories.md).

## Definition

### The functor between the precatory of metric spaces and isometries to the precategory of sets and functions

```agda
module _
  (l1 l2 : Level)
  where

  functor-precategory-set-functions-isometry-Metric-Space :
    functor-Precategory
      (precategory-isometry-Metric-Space {l1} {l2})
      (Set-Precategory l1)
  pr1 functor-precategory-set-functions-isometry-Metric-Space A =
      set-Metric-Space A
  pr2 functor-precategory-set-functions-isometry-Metric-Space =
    ( λ {A B} → map-isometry-Metric-Space A B) ,
    ( ( λ g f → refl) , ( λ A → refl))
```

## Properties

### The precategory functor from metric spaces and isometries to sets and functions is faithful

```agda
module _
  (l1 l2 : Level)
  where

  is-faithful-functor-precategory-set-functions-isometry-Metric-Space :
    is-faithful-functor-Precategory
      (precategory-isometry-Metric-Space)
      (Set-Precategory l1)
      (functor-precategory-set-functions-isometry-Metric-Space l1 l2)
  is-faithful-functor-precategory-set-functions-isometry-Metric-Space A B =
    is-emb-inclusion-subtype (is-isometry-prop-Metric-Space A B)
```

### The precategory functor from metric spaces and isometries to sets and functions is conservative

```agda
module _
  (l1 l2 : Level)
  where

  is-conservative-functor-precategory-set-functions-isometry-Metric-Space :
    is-conservative-functor-Precategory
      (precategory-isometry-Metric-Space)
      (Set-Precategory l1)
      (functor-precategory-set-functions-isometry-Metric-Space l1 l2)
  is-conservative-functor-precategory-set-functions-isometry-Metric-Space
    {A} {B} f H =
    ( isometric-inv) ,
    ( eq-htpy-map-isometry-Metric-Space
      ( B)
      ( B)
      ( comp-isometry-Metric-Space B A B f isometric-inv)
      ( isometry-id-Metric-Space B)
      ( is-section-map-inv-is-equiv is-equiv-f)) ,
    ( eq-htpy-map-isometry-Metric-Space
      ( A)
      ( A)
      ( comp-isometry-Metric-Space A B A isometric-inv f)
      ( isometry-id-Metric-Space A)
      ( is-retraction-map-inv-is-equiv is-equiv-f))
    where

    is-equiv-f : is-equiv (map-isometry-Metric-Space A B f)
    is-equiv-f =
      is-equiv-is-invertible
        ( hom-inv-is-iso-Precategory
          ( Set-Precategory l1)
          { set-Metric-Space A}
          { set-Metric-Space B}
          { map-isometry-Metric-Space A B f}
          ( H))
        ( htpy-eq
          ( is-section-hom-inv-is-iso-Precategory
            ( Set-Precategory l1)
            { set-Metric-Space A}
            { set-Metric-Space B}
            { map-isometry-Metric-Space A B f}
            ( H))) ( htpy-eq
          ( is-retraction-hom-inv-is-iso-Precategory
            ( Set-Precategory l1)
            { set-Metric-Space A}
            { set-Metric-Space B}
            { map-isometry-Metric-Space A B f}
            ( H)))

    isometric-inv : isometry-Metric-Space B A
    isometric-inv =
      isometry-inv-is-equiv-is-isometry-Metric-Space
        ( A)
        ( B)
        ( map-isometry-Metric-Space A B f)
        ( is-equiv-f)
        ( is-isometry-map-isometry-Metric-Space A B f)
```

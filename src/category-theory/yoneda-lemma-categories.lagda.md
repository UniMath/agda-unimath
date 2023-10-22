# The Yoneda lemma for categories

```agda
module category-theory.yoneda-lemma-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.natural-transformations-functors-categories
open import category-theory.natural-transformations-functors-from-small-to-large-precategories
open import category-theory.representable-functors-categories
open import category-theory.yoneda-lemma-precategories

open import foundation.category-of-sets
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [category](category-theory.categories.md) `C`, an object `c`, and a
[functor](category-theory.functors-categories.md) `F` from `C` to the
[category of sets](foundation.category-of-sets.md), there is an
[equivalence](foundation-core.equivalences.md) between the
[set of natural transformations](category-theory.natural-transformations-functors-categories.md)
from the functor
[represented](category-theory.representable-functors-categories.md) by `c` to
`F` and the [set](foundation-core.sets.md) `F c`.

More precisely, the **Yoneda lemma** asserts that the map from the type of
natural transformations to the type `F c` defined by evaluating the component of
the natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## The yoneda lemma into the large category of sets

```agda
module _
  {l1 l2 l3 : Level} (C : Category l1 l2) (c : obj-Category C)
  (F :
    functor-Small-Large-Precategory
      ( precategory-Category C)
      ( Set-Large-Precategory)
      ( l3))
  where

  map-yoneda-Small-Large-Category :
    natural-transformation-Small-Large-Precategory
      ( precategory-Category C)
      ( Set-Large-Precategory)
      ( representable-functor-Category C c)
      ( F) →
    type-Set
      ( obj-functor-Small-Large-Precategory
        ( precategory-Category C)
        ( Set-Large-Precategory)
        ( F)
        ( c))
  map-yoneda-Small-Large-Category σ =
    hom-family-natural-transformation-Small-Large-Precategory
      ( precategory-Category C)
      ( Set-Large-Precategory)
      ( representable-functor-Category C c)
      ( F)
      ( σ)
      ( c)
      ( id-hom-Category C)

  extension-yoneda-Small-Large-Category :
    type-Set
      ( obj-functor-Small-Large-Precategory
        ( precategory-Category C)
        ( Set-Large-Precategory)
        ( F)
        ( c)) →
    natural-transformation-Small-Large-Precategory
      ( precategory-Category C)
      ( Set-Large-Precategory)
      ( representable-functor-Category C c)
      ( F)
  extension-yoneda-Small-Large-Category =
    extension-yoneda-Small-Large-Precategory (precategory-Category C) c F

  lemma-yoneda-Small-Large-Category :
    is-equiv map-yoneda-Small-Large-Category
  lemma-yoneda-Small-Large-Category =
    lemma-yoneda-Small-Large-Precategory (precategory-Category C) c F

  equiv-lemma-yoneda-Small-Large-Category :
    ( natural-transformation-Small-Large-Precategory
      ( precategory-Category C)
      ( Set-Large-Precategory)
      ( representable-functor-Category C c)
      ( F)) ≃
    ( type-Set
      ( obj-functor-Small-Large-Precategory
        ( precategory-Category C)
        ( Set-Large-Precategory)
        ( F)
        ( c)))
  equiv-lemma-yoneda-Small-Large-Category =
    equiv-lemma-yoneda-Small-Large-Precategory (precategory-Category C) c F
```

## The yoneda lemma into the small category of sets

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) (c : obj-Category C)
  (F : functor-Category C (Set-Category l2))
  where

  map-yoneda-Category :
    natural-transformation-Category
      ( C)
      ( Set-Category l2)
      ( representable-functor-Category C c)
      ( F) →
    type-Set (obj-functor-Category C (Set-Category l2) F c)
  map-yoneda-Category = map-yoneda-Precategory (precategory-Category C) c F

  extension-yoneda-Category :
    type-Set (obj-functor-Category C (Set-Category l2) F c) →
    natural-transformation-Category
      C (Set-Category l2) (representable-functor-Category C c) F
  extension-yoneda-Category =
    extension-yoneda-Precategory (precategory-Category C) c F

  lemma-yoneda-Category : is-equiv map-yoneda-Category
  lemma-yoneda-Category = lemma-yoneda-Precategory (precategory-Category C) c F

  equiv-lemma-yoneda-Category :
    ( natural-transformation-Category C (Set-Category l2)
      ( representable-functor-Category C c) F) ≃
    ( type-Set (obj-functor-Category C (Set-Category l2) F c))
  equiv-lemma-yoneda-Category =
    equiv-lemma-yoneda-Precategory (precategory-Category C) c F
```

## See also

- [Presheaf categories](category-theory.presheaf-categories.md)

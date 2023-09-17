# The Yoneda lemma for categories

```agda
module category-theory.yoneda-lemma-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-categories
open import category-theory.natural-transformations-categories
open import category-theory.categories
open import category-theory.representable-functors-categories
open import category-theory.yoneda-lemma-precategories

open import foundation.action-on-identifications-functions
open import foundation.category-of-sets
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [category](category-theory.categories) `C`, an object `c`, and a
[functor](category-theory.functors-categories.md) `F` from `C` to the
[category of Sets](foundation.category-of-sets.md), there is an
[equivalence](foundation-core.equivalenes.md) between the
[set of natural transformations](category-theory.natural-transformations-categories.md)
from the functor
[represented](category-theory.representable-functors-categories.md) by `c` to
`F` and the [set](foundation-core.sets.md) `F c`.

More precisely, the **Yoneda lemma** asserts that the map from the type of
natural transformations to the type `F c` defined by evaluating the component of
the natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## Definition

```agda
module _
  {l1 : Level} (C : Category l1 l1) (c : obj-Category C)
  (F : functor-Category C (Set-Category l1))
  where

  yoneda-evid-Category :
    natural-transformation-Category
      ( C)
      ( Set-Category l1)
      ( rep-functor-Category C c)
      ( F) →
    type-Set (obj-functor-Category C (Set-Category l1) F c)
  yoneda-evid-Category = yoneda-evid-Precategory (precategory-Category C) c F

  yoneda-extension-Category :
    type-Set (obj-functor-Category C (Set-Category l1) F c) →
    natural-transformation-Category
      C (Set-Category l1) (rep-functor-Category C c) F
  yoneda-extension-Category =
    yoneda-extension-Precategory (precategory-Category C) c F

  section-yoneda-evid-Category :
    section yoneda-evid-Category
  section-yoneda-evid-Category =
    section-yoneda-evid-Precategory (precategory-Category C) c F

  retraction-yoneda-evid-Category :
    retraction yoneda-evid-Category
  retraction-yoneda-evid-Category =
    retraction-yoneda-evid-Precategory (precategory-Category C) c F

  yoneda-lemma-Category : is-equiv yoneda-evid-Category
  yoneda-lemma-Category = yoneda-lemma-Precategory (precategory-Category C) c F
```

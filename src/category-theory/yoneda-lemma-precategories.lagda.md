# The Yoneda lemma for precategories

```agda
module category-theory.yoneda-lemma-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-from-small-to-large-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.representable-functors-precategories

open import foundation.action-on-identifications-functions
open import foundation.category-of-sets
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, an object `c`, and
a [functor](category-theory.functors-precategories.md) `F` from `C` to the
[category of sets](foundation.category-of-sets.md), there is an
[equivalence](foundation-core.equivalences.md) between the
[set of natural transformations](category-theory.natural-transformations-functors-precategories.md)
from the functor
[represented](category-theory.representable-functors-precategories.md) by `c` to
`F` and the [set](foundation-core.sets.md) `F c`.

More precisely, the **Yoneda lemma** asserts that the map from the type of
natural transformations to the type `F c` defined by evaluating the component of
the natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## The yoneda lemma into the large category of sets

```agda
module _
  {l1 l2 l3 : Level} (C : Precategory l1 l2) (c : obj-Precategory C)
  (F : functor-Small-Large-Precategory C Set-Large-Precategory l3)
  where

  map-yoneda-Small-Large-Precategory :
    natural-transformation-Small-Large-Precategory
      ( C)
      ( Set-Large-Precategory)
      ( representable-functor-Precategory C c)
      ( F) →
    type-Set (obj-functor-Small-Large-Precategory C Set-Large-Precategory F c)
  map-yoneda-Small-Large-Precategory σ =
    hom-family-natural-transformation-Small-Large-Precategory
      ( C)
      ( Set-Large-Precategory)
      ( representable-functor-Precategory C c)
      ( F)
      ( σ)
      ( c)
      ( id-hom-Precategory C)

  extension-yoneda-Small-Large-Precategory :
    type-Set (obj-functor-Small-Large-Precategory C Set-Large-Precategory F c) →
    natural-transformation-Small-Large-Precategory
      C Set-Large-Precategory (representable-functor-Precategory C c) F
  pr1 (extension-yoneda-Small-Large-Precategory u) x f =
    hom-functor-Small-Large-Precategory C Set-Large-Precategory F f u
  pr2 (extension-yoneda-Small-Large-Precategory u) g =
    eq-htpy
      ( λ f →
        htpy-eq
          ( inv
            ( preserves-comp-functor-Small-Large-Precategory
              ( C)
              ( Set-Large-Precategory)
              ( F)
              ( g)
              ( f)))
          ( u))

  section-map-yoneda-Small-Large-Precategory :
    section map-yoneda-Small-Large-Precategory
  pr1 section-map-yoneda-Small-Large-Precategory =
    extension-yoneda-Small-Large-Precategory
  pr2 section-map-yoneda-Small-Large-Precategory =
    htpy-eq
      ( preserves-id-functor-Small-Large-Precategory
        ( C)
        ( Set-Large-Precategory)
        ( F)
        ( c))

  retraction-map-yoneda-Small-Large-Precategory :
    retraction map-yoneda-Small-Large-Precategory
  pr1 retraction-map-yoneda-Small-Large-Precategory =
    extension-yoneda-Small-Large-Precategory
  pr2 retraction-map-yoneda-Small-Large-Precategory σ =
    eq-type-subtype
      ( is-natural-transformation-prop-Small-Large-Precategory
        ( C) Set-Large-Precategory (representable-functor-Precategory C c) F)
      ( eq-htpy
        ( λ x →
          eq-htpy
            ( λ f →
              ( htpy-eq
                ( pr2 σ f)
                ( (id-hom-Precategory C))) ∙
              ( ap (pr1 σ x) (right-unit-law-comp-hom-Precategory C f)))))

  lemma-yoneda-Small-Large-Precategory :
    is-equiv map-yoneda-Small-Large-Precategory
  pr1 lemma-yoneda-Small-Large-Precategory =
    section-map-yoneda-Small-Large-Precategory
  pr2 lemma-yoneda-Small-Large-Precategory =
    retraction-map-yoneda-Small-Large-Precategory

  equiv-lemma-yoneda-Small-Large-Precategory :
    ( natural-transformation-Small-Large-Precategory C Set-Large-Precategory
      ( representable-functor-Precategory C c) (F)) ≃
    ( type-Set
      ( obj-functor-Small-Large-Precategory C Set-Large-Precategory F c))
  pr1 equiv-lemma-yoneda-Small-Large-Precategory =
    map-yoneda-Small-Large-Precategory
  pr2 equiv-lemma-yoneda-Small-Large-Precategory =
    lemma-yoneda-Small-Large-Precategory
```

## The yoneda lemma into the small category of sets

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (c : obj-Precategory C)
  (F : functor-Precategory C (Set-Precategory l2))
  where

  map-yoneda-Precategory :
    natural-transformation-Precategory
      ( C)
      ( Set-Precategory l2)
      ( representable-functor-Precategory C c)
      ( F) →
    type-Set (obj-functor-Precategory C (Set-Precategory l2) F c)
  map-yoneda-Precategory = map-yoneda-Small-Large-Precategory C c F

  extension-yoneda-Precategory :
    type-Set (obj-functor-Precategory C (Set-Precategory l2) F c) →
    natural-transformation-Precategory
      C (Set-Precategory l2) (representable-functor-Precategory C c) F
  extension-yoneda-Precategory = extension-yoneda-Small-Large-Precategory C c F

  lemma-yoneda-Precategory : is-equiv map-yoneda-Precategory
  lemma-yoneda-Precategory = lemma-yoneda-Small-Large-Precategory C c F

  equiv-lemma-yoneda-Precategory :
    ( natural-transformation-Precategory C (Set-Precategory l2)
      ( representable-functor-Precategory C c) F) ≃
    ( type-Set (obj-functor-Precategory C (Set-Precategory l2) F c))
  equiv-lemma-yoneda-Precategory =
    equiv-lemma-yoneda-Small-Large-Precategory C c F
```

## See also

- [Presheaf categories](category-theory.presheaf-categories.md)

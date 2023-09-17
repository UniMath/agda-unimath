# The Yoneda lemma for precategories

```agda
module category-theory.yoneda-lemma-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.precategories
open import category-theory.representable-functors-precategories

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
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, an object `c`, and
a [functor](category-theory.functors-precategories.md) `F` from `C` to the
[precategory of Sets](foundation.category-of-sets.md), there is an
[equivalence](foundation-core.equivalences.md) between the
[set of natural transformations](category-theory.natural-transformations-precategories.md)
from the functor
[represented](category-theory.representable-functors-precategories.md) by `c` to
`F` and the [set](foundation-core.sets.md) `F c`.

More precisely, the **Yoneda lemma** asserts that the map from the type of
natural transformations to the type `F c` defined by evaluating the component of
the natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (c : obj-Precategory C)
  (F : functor-Precategory C (Set-Precategory l2))
  where

  yoneda-evid-Precategory :
    natural-transformation-Precategory
      ( C)
      ( Set-Precategory l2)
      ( rep-functor-Precategory C c)
      ( F) →
    type-Set (obj-functor-Precategory C (Set-Precategory l2) F c)
  yoneda-evid-Precategory α =
    components-natural-transformation-Precategory
      ( C)
      ( Set-Precategory l2)
      ( rep-functor-Precategory C c)
      ( F)
      ( α)
      ( c)
      ( id-hom-Precategory C)

  yoneda-extension-Precategory :
    type-Set (obj-functor-Precategory C (Set-Precategory l2) F c) →
    natural-transformation-Precategory
      C (Set-Precategory l2) (rep-functor-Precategory C c) F
  pr1 (yoneda-extension-Precategory u) x f =
    hom-functor-Precategory C (Set-Precategory l2) F f u
  pr2 (yoneda-extension-Precategory u) g =
    eq-htpy
      ( λ f →
        htpy-eq
          ( inv
            ( preserves-comp-functor-Precategory C (Set-Precategory l2) F g f))
          ( u))

  section-yoneda-evid-Precategory :
    section yoneda-evid-Precategory
  pr1 section-yoneda-evid-Precategory = yoneda-extension-Precategory
  pr2 section-yoneda-evid-Precategory =
    htpy-eq (preserves-id-functor-Precategory C (Set-Precategory l2) F c)

  retraction-yoneda-evid-Precategory :
    retraction yoneda-evid-Precategory
  pr1 retraction-yoneda-evid-Precategory = yoneda-extension-Precategory
  pr2 retraction-yoneda-evid-Precategory α =
    eq-type-subtype
      ( is-natural-transformation-Precategory-Prop
        ( C) (Set-Precategory l2) (rep-functor-Precategory C c) F)
      ( eq-htpy
        ( λ x →
          eq-htpy
            ( λ f →
              ( htpy-eq
                ( (pr2 α) f)
                ( (id-hom-Precategory C))) ∙
              ( ap (pr1 α x) (right-unit-law-comp-hom-Precategory C f)))))

  yoneda-lemma-Precategory : is-equiv yoneda-evid-Precategory
  pr1 yoneda-lemma-Precategory = section-yoneda-evid-Precategory
  pr2 yoneda-lemma-Precategory = retraction-yoneda-evid-Precategory

  equiv-yoneda-lemma-Precategory :
    ( natural-transformation-Precategory C (Set-Precategory l2)
      ( rep-functor-Precategory C c) (F)) ≃
    ( type-Set (obj-functor-Precategory C (Set-Precategory l2) F c))
  pr1 equiv-yoneda-lemma-Precategory = yoneda-evid-Precategory
  pr2 equiv-yoneda-lemma-Precategory = yoneda-lemma-Precategory
```

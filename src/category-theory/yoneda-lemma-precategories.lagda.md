# Yoneda lemma for precategories

```agda
module category-theory.yoneda-lemma-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.precategories
open import category-theory.representable-functors-precategories

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

Given a precategory `C`, an object `c`, and a functor `F` from `C` to the
precategory of Sets, there is an equivalence between the set of natural
transformations from the functor represented by `c` to `F` and the set `F c`.

More precisely, the Yoneda lemma asserts that the map from the type of natural
transformations to the type `F c` defined by evaluating the component of the
natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## Definition

```agda
module _
  {l1 : Level} (C : Precategory l1 l1) (c : obj-Precategory C)
  (F : functor-Precategory C (Set-Precategory l1))
  where

  yoneda-evid-Precategory :
    natural-transformation-Precategory C (Set-Precategory l1)
    (rep-functor-Precategory C c) F →
    type-Set (obj-functor-Precategory C (Set-Precategory l1) F c)
  yoneda-evid-Precategory α =
    ( components-natural-transformation-Precategory C (Set-Precategory _)
    ( rep-functor-Precategory C c) F α c) (id-hom-Precategory C)

  yoneda-extension-Precategory :
    type-Set (obj-functor-Precategory C (Set-Precategory l1) F c) →
    natural-transformation-Precategory C (Set-Precategory l1)
    (rep-functor-Precategory C c) F
  pr1 (yoneda-extension-Precategory u) x f =
    hom-functor-Precategory C (Set-Precategory _) F f u
  pr2 (yoneda-extension-Precategory u) g =
    eq-htpy
      ( λ f →
        htpy-eq
          ( inv
            ( preserves-comp-functor-Precategory C (Set-Precategory _) F g f))
          u)

  sec-yoneda-evid-Precategory :
    sec yoneda-evid-Precategory
  pr1 sec-yoneda-evid-Precategory = yoneda-extension-Precategory
  pr2 sec-yoneda-evid-Precategory =
    λ u →
      htpy-eq (preserves-id-functor-Precategory C (Set-Precategory _) F c) u

  retr-yoneda-evid-Precategory :
    retr yoneda-evid-Precategory
  pr1 retr-yoneda-evid-Precategory = yoneda-extension-Precategory
  pr2 retr-yoneda-evid-Precategory =
    λ α → eq-pair-Σ
            ( eq-htpy
              ( λ x →
                eq-htpy
                  ( λ f →
                    htpy-eq ((pr2 α) f) ((id-hom-Precategory C {c})) ∙
                    ap (pr1 α x) (right-unit-law-comp-hom-Precategory C f))))
            ( eq-is-prop'
              ( is-prop-is-natural-transformation-Precategory
                C (Set-Precategory _)
                (( rep-functor-Precategory C c)) F
                ( pr1 α)) _ (pr2 α))

  yoneda-lemma-Precategory : is-equiv yoneda-evid-Precategory
  yoneda-lemma-Precategory =
    sec-yoneda-evid-Precategory , retr-yoneda-evid-Precategory
```

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

open import foundation-core.homotopies
open import foundation-core.identity-types

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a precategory `C`, an object `c`, and a functor `F` from `C` to the
precategory of Sets, there is an equivalence between the set of natural
transformations from the functor represented by `c` to `F` and the set `F c`.

More precisely, the Yoneda lemma asserts that the map from the set of natural
transformations to the set `F c` defined by evaluating the component of the
natural transformation at the object `c` at the identity arrow on `c` is an
equivalence.

## Definition

```agda
yoneda-evid-Precategory :
  {l1 l2 : Level} (C : Precategory l1 (l1)) (c : obj-Precategory C)
  (F : functor-Precategory C (Set-Precategory (l1))) →
  natural-transformation-Precategory C (Set-Precategory (l1))
  (rep-functor-Precategory C c) F →
  type-Set (obj-functor-Precategory C (Set-Precategory (l1)) F c)
yoneda-evid-Precategory C c F α =
  ( components-natural-transformation-Precategory C (Set-Precategory _)
  ( rep-functor-Precategory C c) F α c) (id-hom-Precategory C)

yoneda-extension-Precategory :
  {l1 : Level} (C : Precategory l1 (l1)) (c : obj-Precategory C)
  (F : functor-Precategory C (Set-Precategory (l1))) →
  type-Set (obj-functor-Precategory C (Set-Precategory (l1)) F c) →
  natural-transformation-Precategory C (Set-Precategory (l1))
  (rep-functor-Precategory C c) F
pr1 (yoneda-extension-Precategory C c F u) x f =
  hom-functor-Precategory C (Set-Precategory _) F f u
pr2 (yoneda-extension-Precategory C c F u) g =
  eq-htpy
    ( λ f →
      htpy-eq
        ( inv
          ( preserves-comp-functor-Precategory C (Set-Precategory _) F g f)) u)
```

# Pointed endofunctors on categories

```agda
module category-theory.pointed-endofunctors-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-categories
open import category-theory.natural-transformations-functors-categories
open import category-theory.pointed-endofunctors-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

An [endofunctor](category-theory.functors-categories.md) `F : C → C` on a
[category](category-theory.categories.md) `C` is said to be
{{#concept "pointed" Disambiguation="endofunctor on a category" Agda=pointed-endofunctor-Category}}
if it comes equipped with a
[natural transformation](category-theory.natural-transformations-functors-categories.md)
`id ⇒ F` from the identity [functor](category-theory.functors-categories.md) to
`F`.

More explicitly, a
{{#concept "pointing" Disambiguation="endofunctor on a category" Agda=pointing-endofunctor-Category}}
of an endofunctor `F : C → C` consists of a family of morphisms `η X : X → F X`
such that for each morphism `f : X → Y` in `C` the diagram

```text
       η X
    X -----> F X
    |         |
  f |         | F f
    ∨         ∨
    Y -----> F Y
       η Y
```

[commutes](category-theory.commuting-squares-of-morphisms-in-precategories.md).

## Definitions

### The structure of a pointing on an endofunctor on a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) (T : functor-Category C C)
  where

  pointing-endofunctor-Category : UU (l1 ⊔ l2)
  pointing-endofunctor-Category =
    pointing-endofunctor-Precategory (precategory-Category C) T
```

### Pointed endofunctors on a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  pointed-endofunctor-Category : UU (l1 ⊔ l2)
  pointed-endofunctor-Category =
    pointed-endofunctor-Precategory (precategory-Category C)

  module _
    (F : pointed-endofunctor-Category)
    where

    functor-pointed-endofunctor-Category :
      functor-Category C C
    functor-pointed-endofunctor-Category =
      functor-pointed-endofunctor-Precategory (precategory-Category C) F

    obj-pointed-endofunctor-Category : obj-Category C → obj-Category C
    obj-pointed-endofunctor-Category =
      obj-pointed-endofunctor-Precategory (precategory-Category C) F

    hom-pointed-endofunctor-Category :
      {X Y : obj-Category C} →
      hom-Category C X Y →
      hom-Category C
        ( obj-pointed-endofunctor-Category X)
        ( obj-pointed-endofunctor-Category Y)
    hom-pointed-endofunctor-Category =
      hom-pointed-endofunctor-Precategory (precategory-Category C) F

    preserves-id-pointed-endofunctor-Category :
      (X : obj-Category C) →
      hom-pointed-endofunctor-Category (id-hom-Category C {X}) ＝
      id-hom-Category C
    preserves-id-pointed-endofunctor-Category =
      preserves-id-pointed-endofunctor-Precategory (precategory-Category C) F

    preserves-comp-pointed-endofunctor-Category :
      {X Y Z : obj-Category C}
      (g : hom-Category C Y Z) (f : hom-Category C X Y) →
      hom-pointed-endofunctor-Category
        ( comp-hom-Category C g f) ＝
      comp-hom-Category C
        ( hom-pointed-endofunctor-Category g)
        ( hom-pointed-endofunctor-Category f)
    preserves-comp-pointed-endofunctor-Category =
      preserves-comp-pointed-endofunctor-Precategory (precategory-Category C) F

    pointing-pointed-endofunctor-Category :
      natural-transformation-Category C C
        ( id-functor-Category C)
        ( functor-pointed-endofunctor-Category)
    pointing-pointed-endofunctor-Category =
      pointing-pointed-endofunctor-Precategory (precategory-Category C) F

    hom-family-pointing-pointed-endofunctor-Category :
      hom-family-functor-Category C C
        ( id-functor-Category C)
        ( functor-pointed-endofunctor-Category)
    hom-family-pointing-pointed-endofunctor-Category =
      hom-family-pointing-pointed-endofunctor-Precategory
        ( precategory-Category C)
        ( F)

    naturality-pointing-pointed-endofunctor-Category :
      is-natural-transformation-Category C C
        ( id-functor-Category C)
        ( functor-pointed-endofunctor-Category)
        ( hom-family-pointing-pointed-endofunctor-Category)
    naturality-pointing-pointed-endofunctor-Category =
      naturality-pointing-pointed-endofunctor-Precategory
        ( precategory-Category C) F
```

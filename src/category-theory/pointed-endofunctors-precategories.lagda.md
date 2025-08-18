# Pointed endofunctors on precategories

```agda
module category-theory.pointed-endofunctors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

An [endofunctor](category-theory.functors-precategories.md) `F : C → C` on a
[precategory](category-theory.precategories.md) `C` is said to be
{{#concept "pointed" Disambiguation="endofunctor on a category" Agda=pointed-endofunctor-Precategory}}
if it comes equipped with a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
`id ⇒ F` from the identity [functor](category-theory.functors-precategories.md)
to `F`.

More explicitly, a
{{#concept "pointing" Disambiguation="endofunctor on a precategory" Agda=pointing-endofunctor-Precategory}}
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

### The structure of a pointing on an endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (T : functor-Precategory C C)
  where

  pointing-endofunctor-Precategory : UU (l1 ⊔ l2)
  pointing-endofunctor-Precategory =
    natural-transformation-Precategory C C (id-functor-Precategory C) T
```

### Pointed endofunctors on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  pointed-endofunctor-Precategory =
    Σ (functor-Precategory C C) (pointing-endofunctor-Precategory C)

  module _
    (F : pointed-endofunctor-Precategory)
    where

    functor-pointed-endofunctor-Precategory :
      functor-Precategory C C
    functor-pointed-endofunctor-Precategory =
      pr1 F

    obj-pointed-endofunctor-Precategory : obj-Precategory C → obj-Precategory C
    obj-pointed-endofunctor-Precategory =
      obj-functor-Precategory C C functor-pointed-endofunctor-Precategory

    hom-pointed-endofunctor-Precategory :
      {X Y : obj-Precategory C} →
      hom-Precategory C X Y →
      hom-Precategory C
        ( obj-pointed-endofunctor-Precategory X)
        ( obj-pointed-endofunctor-Precategory Y)
    hom-pointed-endofunctor-Precategory =
      hom-functor-Precategory C C functor-pointed-endofunctor-Precategory

    preserves-id-pointed-endofunctor-Precategory :
      (X : obj-Precategory C) →
      hom-pointed-endofunctor-Precategory (id-hom-Precategory C {X}) ＝
      id-hom-Precategory C
    preserves-id-pointed-endofunctor-Precategory =
      preserves-id-functor-Precategory C C
        ( functor-pointed-endofunctor-Precategory)

    preserves-comp-pointed-endofunctor-Precategory :
      {X Y Z : obj-Precategory C}
      (g : hom-Precategory C Y Z) (f : hom-Precategory C X Y) →
      hom-pointed-endofunctor-Precategory
        ( comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C
        ( hom-pointed-endofunctor-Precategory g)
        ( hom-pointed-endofunctor-Precategory f)
    preserves-comp-pointed-endofunctor-Precategory =
      preserves-comp-functor-Precategory C C
        ( functor-pointed-endofunctor-Precategory)

    pointing-pointed-endofunctor-Precategory :
      natural-transformation-Precategory C C
        ( id-functor-Precategory C)
        ( functor-pointed-endofunctor-Precategory)
    pointing-pointed-endofunctor-Precategory = pr2 F

    hom-family-pointing-pointed-endofunctor-Precategory :
      hom-family-functor-Precategory C C
        ( id-functor-Precategory C)
        ( functor-pointed-endofunctor-Precategory)
    hom-family-pointing-pointed-endofunctor-Precategory =
      hom-family-natural-transformation-Precategory C C
        ( id-functor-Precategory C)
        ( functor-pointed-endofunctor-Precategory)
        ( pointing-pointed-endofunctor-Precategory)

    naturality-pointing-pointed-endofunctor-Precategory :
      is-natural-transformation-Precategory C C
        ( id-functor-Precategory C)
        ( functor-pointed-endofunctor-Precategory)
        ( hom-family-pointing-pointed-endofunctor-Precategory)
    naturality-pointing-pointed-endofunctor-Precategory =
      naturality-natural-transformation-Precategory C C
        ( id-functor-Precategory C)
        ( functor-pointed-endofunctor-Precategory)
        ( pointing-pointed-endofunctor-Precategory)
```

## See also

- [Copointed endofunctors](category-theory.copointed-endofunctors-precategories.md)
  for the dual concept.

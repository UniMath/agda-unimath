# Copointed endofunctors on precategories

```agda
module category-theory.copointed-endofunctors-precategories where
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
{{#concept "copointed" Disambiguation="endofunctor on a category" Agda=copointed-endofunctor-Precategory}}
if it comes equipped with a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
`F ⇒ id` from `F` to the identity
[functor](category-theory.functors-precategories.md).

More explicitly, a
{{#concept "copointing" Disambiguation="endofunctor on a precategory" Agda=copointing-endofunctor-Precategory}}
of an endofunctor `F : C → C` consists of a family of morphisms `ε X : F X → X`
such that for each morphism `f : X → Y` in `C` the diagram

```text
           ε X
      F X -----> X
       |         |
  F f  |         | f
       ∨         ∨
      F Y -----> Y
           ε Y
```

[commutes](category-theory.commuting-squares-of-morphisms-in-precategories.md).

## Definitions

### The structure of a copointing on an endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (T : functor-Precategory C C)
  where

  copointing-endofunctor-Precategory : UU (l1 ⊔ l2)
  copointing-endofunctor-Precategory =
    natural-transformation-Precategory C C T (id-functor-Precategory C)
```

### Copointed endofunctors on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  copointed-endofunctor-Precategory =
    Σ (functor-Precategory C C) (copointing-endofunctor-Precategory C)

  module _
    (F : copointed-endofunctor-Precategory)
    where

    functor-copointed-endofunctor-Precategory :
      functor-Precategory C C
    functor-copointed-endofunctor-Precategory =
      pr1 F

    obj-copointed-endofunctor-Precategory :
      obj-Precategory C → obj-Precategory C
    obj-copointed-endofunctor-Precategory =
      obj-functor-Precategory C C functor-copointed-endofunctor-Precategory

    hom-copointed-endofunctor-Precategory :
      {X Y : obj-Precategory C} →
      hom-Precategory C X Y →
      hom-Precategory C
        ( obj-copointed-endofunctor-Precategory X)
        ( obj-copointed-endofunctor-Precategory Y)
    hom-copointed-endofunctor-Precategory =
      hom-functor-Precategory C C functor-copointed-endofunctor-Precategory

    preserves-id-copointed-endofunctor-Precategory :
      (X : obj-Precategory C) →
      hom-copointed-endofunctor-Precategory (id-hom-Precategory C {X}) ＝
      id-hom-Precategory C
    preserves-id-copointed-endofunctor-Precategory =
      preserves-id-functor-Precategory C C
        ( functor-copointed-endofunctor-Precategory)

    preserves-comp-copointed-endofunctor-Precategory :
      {X Y Z : obj-Precategory C}
      (g : hom-Precategory C Y Z) (f : hom-Precategory C X Y) →
      hom-copointed-endofunctor-Precategory
        ( comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C
        ( hom-copointed-endofunctor-Precategory g)
        ( hom-copointed-endofunctor-Precategory f)
    preserves-comp-copointed-endofunctor-Precategory =
      preserves-comp-functor-Precategory C C
        ( functor-copointed-endofunctor-Precategory)

    copointing-copointed-endofunctor-Precategory :
      natural-transformation-Precategory C C
        ( functor-copointed-endofunctor-Precategory)
        ( id-functor-Precategory C)
    copointing-copointed-endofunctor-Precategory = pr2 F

    hom-family-copointing-copointed-endofunctor-Precategory :
      hom-family-functor-Precategory C C
        ( functor-copointed-endofunctor-Precategory)
        ( id-functor-Precategory C)
    hom-family-copointing-copointed-endofunctor-Precategory =
      hom-family-natural-transformation-Precategory C C
        ( functor-copointed-endofunctor-Precategory)
        ( id-functor-Precategory C)
        ( copointing-copointed-endofunctor-Precategory)

    naturality-copointing-copointed-endofunctor-Precategory :
      is-natural-transformation-Precategory C C
        ( functor-copointed-endofunctor-Precategory)
        ( id-functor-Precategory C)
        ( hom-family-copointing-copointed-endofunctor-Precategory)
    naturality-copointing-copointed-endofunctor-Precategory =
      naturality-natural-transformation-Precategory C C
        ( functor-copointed-endofunctor-Precategory)
        ( id-functor-Precategory C)
        ( copointing-copointed-endofunctor-Precategory)
```

## See also

- [Pointed endofunctors](category-theory.pointed-endofunctors-precategories.md)
  for the dual concept.

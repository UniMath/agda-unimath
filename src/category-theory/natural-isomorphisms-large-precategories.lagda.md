# Natural isomorphisms between functors between large precategories

```agda
module category-theory.natural-isomorphisms-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-large-precategories

open import foundation.universe-levels
```

</details>

## Idea

A **natural isomorphism** `γ` from
[functor](category-theory.functors-large-precategories.md) `F : C → D` to
`G : C → D` is a
[natural transformation](category-theory.natural-transformations-large-precategories.md)
from `F` to `G` such that the morphism `γ x : hom (F x) (G x)` is an
[isomorphism](category-theory.isomorphisms-in-precategories.md), for every
object `x` in `C`.

## Definition

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC}
  {D : Large-Precategory αD βD}
  (F : functor-Large-Precategory C D γF)
  (G : functor-Large-Precategory C D γG)
  where

  iso-family-functor-Large-Precategory : UUω
  iso-family-functor-Large-Precategory =
    { l : Level}
    ( X : obj-Large-Precategory C l) →
    iso-Large-Precategory D
      ( obj-functor-Large-Precategory F X)
      ( obj-functor-Large-Precategory G X)

  record natural-isomorphism-Large-Precategory : UUω
    where
    constructor make-natural-isomorphism
    field
      components-natural-isomorphism-Large-Precategory :
        iso-family-functor-Large-Precategory
      coherence-square-natural-isomorphism-Large-Precategory :
        { l1 l2 : Level}
        { X : obj-Large-Precategory C l1}
        { Y : obj-Large-Precategory C l2}
        ( f : hom-Large-Precategory C X Y) →
        coherence-square-Large-Precategory D
          ( hom-iso-Large-Precategory D
            ( components-natural-isomorphism-Large-Precategory X))
          ( hom-functor-Large-Precategory F f)
          ( hom-functor-Large-Precategory G f)
          ( hom-iso-Large-Precategory D
            ( components-natural-isomorphism-Large-Precategory Y))

  open natural-isomorphism-Large-Precategory public

  natural-transformation-natural-isomorphism-Large-Precategory :
    natural-isomorphism-Large-Precategory →
    natural-transformation-Large-Precategory F G
  hom-family-natural-transformation-Large-Precategory
    ( natural-transformation-natural-isomorphism-Large-Precategory γ) X =
    hom-iso-Large-Precategory D
      ( components-natural-isomorphism-Large-Precategory γ X)
  coherence-square-natural-transformation-Large-Precategory
    (natural-transformation-natural-isomorphism-Large-Precategory γ) =
      coherence-square-natural-isomorphism-Large-Precategory γ
```

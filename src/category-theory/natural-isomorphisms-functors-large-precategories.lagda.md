# Natural isomorphisms between functors between large precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.natural-isomorphisms-functors-large-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategories funext univalence truncations
open import category-theory.functors-large-precategories funext univalence truncations
open import category-theory.isomorphisms-in-large-precategories funext univalence truncations
open import category-theory.large-precategories funext univalence truncations
open import category-theory.natural-transformations-functors-large-precategories funext univalence truncations

open import foundation.universe-levels
```

</details>

## Idea

A **natural isomorphism** `γ` from
[functor](category-theory.functors-large-precategories.md) `F : C → D` to
`G : C → D` is a
[natural transformation](category-theory.natural-transformations-functors-large-precategories.md)
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
  (F : functor-Large-Precategory γF C D)
  (G : functor-Large-Precategory γG C D)
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
      iso-natural-isomorphism-Large-Precategory :
        iso-family-functor-Large-Precategory
      naturality-natural-isomorphism-Large-Precategory :
        { l1 l2 : Level}
        { X : obj-Large-Precategory C l1}
        { Y : obj-Large-Precategory C l2}
        ( f : hom-Large-Precategory C X Y) →
        coherence-square-hom-Large-Precategory D
          ( hom-functor-Large-Precategory F f)
          ( hom-iso-Large-Precategory D
            ( iso-natural-isomorphism-Large-Precategory X))
          ( hom-iso-Large-Precategory D
            ( iso-natural-isomorphism-Large-Precategory Y))
          ( hom-functor-Large-Precategory G f)

  open natural-isomorphism-Large-Precategory public

  natural-transformation-natural-isomorphism-Large-Precategory :
    natural-isomorphism-Large-Precategory →
    natural-transformation-Large-Precategory C D F G
  hom-natural-transformation-Large-Precategory
    ( natural-transformation-natural-isomorphism-Large-Precategory γ) X =
    hom-iso-Large-Precategory D
      ( iso-natural-isomorphism-Large-Precategory γ X)
  naturality-natural-transformation-Large-Precategory
    ( natural-transformation-natural-isomorphism-Large-Precategory γ) =
      naturality-natural-isomorphism-Large-Precategory γ
```

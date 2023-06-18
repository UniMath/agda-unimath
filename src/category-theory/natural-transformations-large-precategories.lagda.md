# Natural transformations between functors between large precategories

```agda
module category-theory.natural-transformations-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories

open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given large precategories `C` and `D`, a natural transformation from a functor
`F : C → D` to `G : C → D` consists of :

- a family of morphisms `γ : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (γ x) = (γ y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
square-Large-Precategory :
  {αC : Level → Level} {βC : Level → Level → Level} →
  (C : Large-Precategory αC βC) →
  {l1 l2 l3 l4 : Level} →
  {A : obj-Large-Precategory C l1} {B : obj-Large-Precategory C l2} →
  {X : obj-Large-Precategory C l3} {Y : obj-Large-Precategory C l4} →
  (top : type-hom-Large-Precategory C A B)
  (left : type-hom-Large-Precategory C A X) →
  (right : type-hom-Large-Precategory C B Y)
  (bottom : type-hom-Large-Precategory C X Y) →
  UU (βC l1 l4)
square-Large-Precategory C top left right bottom =
  comp-hom-Large-Precategory C bottom left ＝
  comp-hom-Large-Precategory C right top

module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC} {D : Large-Precategory αD βD}
  (F : functor-Large-Precategory C D γF) (G : functor-Large-Precategory C D γG)
  where

  record natural-transformation-Large-Precategory : UUω
    where
    constructor make-natural-transformation
    field
      obj-natural-transformation-Large-Precategory :
        {l1 : Level} (X : obj-Large-Precategory C l1) →
        type-hom-Large-Precategory D
          ( obj-functor-Large-Precategory F X)
          ( obj-functor-Large-Precategory G X)
      coherence-square-natural-transformation-Large-Precategory :
        {l1 l2 : Level} {X : obj-Large-Precategory C l1}
        {Y : obj-Large-Precategory C l2}
        (f : type-hom-Large-Precategory C X Y) →
        square-Large-Precategory D
          ( obj-natural-transformation-Large-Precategory X)
          ( hom-functor-Large-Precategory F f)
          ( hom-functor-Large-Precategory G f)
          ( obj-natural-transformation-Large-Precategory Y)

  open natural-transformation-Large-Precategory public
```

## Examples

### The identity natural transformation

Every functor comes equipped with an identity natural transformation.

```agda
id-natural-transformation-Large-Precategory :
  { αC αD γF γG : Level → Level}
  { βC βD : Level → Level → Level} →
  { C : Large-Precategory αC βC} {D : Large-Precategory αD βD} →
  ( F : functor-Large-Precategory C D γF) →
  natural-transformation-Large-Precategory F F
obj-natural-transformation-Large-Precategory
  ( id-natural-transformation-Large-Precategory {D = D} F) X =
    id-hom-Large-Precategory D
coherence-square-natural-transformation-Large-Precategory
  ( id-natural-transformation-Large-Precategory {D = D} F) f =
  ( left-unit-law-comp-hom-Large-Precategory D
    ( hom-functor-Large-Precategory F f)) ∙
  ( inv
    ( right-unit-law-comp-hom-Large-Precategory D
      ( hom-functor-Large-Precategory F f)))
```

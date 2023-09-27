# Natural transformations between functors between large precategories

```agda
module category-theory.natural-transformations-functors-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given [large precategories](category-theory.large-precategories.md) `C` and `D`,
a **natural transformation** from a
[functor](category-theory.functors-large-precategories.md) `F : C → D` to
`G : C → D` consists of :

- a family of morphisms `γ : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (γ x) = (γ y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
coherence-square-Large-Precategory :
  {αC : Level → Level}
  {βC : Level → Level → Level}
  (C : Large-Precategory αC βC)
  {l1 l2 l3 l4 : Level}
  {A : obj-Large-Precategory C l1}
  {B : obj-Large-Precategory C l2}
  {X : obj-Large-Precategory C l3}
  {Y : obj-Large-Precategory C l4}
  (top : hom-Large-Precategory C A B)
  (left : hom-Large-Precategory C A X)
  (right : hom-Large-Precategory C B Y)
  (bottom : hom-Large-Precategory C X Y) →
  UU (βC l1 l4)
coherence-square-Large-Precategory C top left right bottom =
  comp-hom-Large-Precategory C right top ＝
  comp-hom-Large-Precategory C bottom left

module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC}
  {D : Large-Precategory αD βD}
  (F : functor-Large-Precategory C D γF)
  (G : functor-Large-Precategory C D γG)
  where

  hom-family-functor-Large-Precategory : UUω
  hom-family-functor-Large-Precategory =
    {l : Level} (X : obj-Large-Precategory C l) →
    hom-Large-Precategory D
      ( obj-functor-Large-Precategory F X)
      ( obj-functor-Large-Precategory G X)

  record natural-transformation-Large-Precategory : UUω
    where
    constructor make-natural-transformation
    field
      hom-family-natural-transformation-Large-Precategory :
        hom-family-functor-Large-Precategory
      coherence-square-natural-transformation-Large-Precategory :
        {l1 l2 : Level} {X : obj-Large-Precategory C l1}
        {Y : obj-Large-Precategory C l2}
        (f : hom-Large-Precategory C X Y) →
        coherence-square-Large-Precategory D
          ( hom-family-natural-transformation-Large-Precategory X)
          ( hom-functor-Large-Precategory F f)
          ( hom-functor-Large-Precategory G f)
          ( hom-family-natural-transformation-Large-Precategory Y)

  open natural-transformation-Large-Precategory public
```

## Properties

### The identity natural transformation

Every functor comes equipped with an identity natural transformation.

```agda
module _
  { αC αD γF : Level → Level}
  { βC βD : Level → Level → Level}
  { C : Large-Precategory αC βC}
  { D : Large-Precategory αD βD}
  where

  id-natural-transformation-Large-Precategory :
    ( F : functor-Large-Precategory C D γF) →
    natural-transformation-Large-Precategory F F
  hom-family-natural-transformation-Large-Precategory
    ( id-natural-transformation-Large-Precategory F) X =
      id-hom-Large-Precategory D
  coherence-square-natural-transformation-Large-Precategory
    ( id-natural-transformation-Large-Precategory F) f =
        ( right-unit-law-comp-hom-Large-Precategory D
          ( hom-functor-Large-Precategory F f)) ∙
        ( inv
          ( left-unit-law-comp-hom-Large-Precategory D
            ( hom-functor-Large-Precategory F f)))
```

### Composition of natural transformations

```agda
module _
  {αC αD γF γG γH : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC}
  {D : Large-Precategory αD βD}
  (F : functor-Large-Precategory C D γF)
  (G : functor-Large-Precategory C D γG)
  (H : functor-Large-Precategory C D γH)
  where

  comp-natural-transformation-Large-Precategory :
    natural-transformation-Large-Precategory G H →
    natural-transformation-Large-Precategory F G →
    natural-transformation-Large-Precategory F H
  hom-family-natural-transformation-Large-Precategory
    ( comp-natural-transformation-Large-Precategory b a) X =
      comp-hom-Large-Precategory D
        ( hom-family-natural-transformation-Large-Precategory b X)
        ( hom-family-natural-transformation-Large-Precategory a X)
  coherence-square-natural-transformation-Large-Precategory
    ( comp-natural-transformation-Large-Precategory b a) {X = X} {Y} f =
    ( inv
      ( associative-comp-hom-Large-Precategory D
        ( hom-functor-Large-Precategory H f)
        ( hom-family-natural-transformation-Large-Precategory b X)
        ( hom-family-natural-transformation-Large-Precategory a X))) ∙
    ( ap
      ( comp-hom-Large-Precategory' D
        ( hom-family-natural-transformation-Large-Precategory a X))
      ( coherence-square-natural-transformation-Large-Precategory b f)) ∙
    ( associative-comp-hom-Large-Precategory D
      ( hom-family-natural-transformation-Large-Precategory b Y)
      ( hom-functor-Large-Precategory G f)
      ( hom-family-natural-transformation-Large-Precategory a X)) ∙
    ( ap
      ( comp-hom-Large-Precategory D
        ( hom-family-natural-transformation-Large-Precategory b Y))
      ( coherence-square-natural-transformation-Large-Precategory a f)) ∙
    ( inv
      ( associative-comp-hom-Large-Precategory D
        ( hom-family-natural-transformation-Large-Precategory b Y)
        ( hom-family-natural-transformation-Large-Precategory a Y)
        ( hom-functor-Large-Precategory F f)))
```

## See also

- [Homotopies of natural transformations in large precategories](category-theory.homotopies-natural-transformations-large-precategories.md)

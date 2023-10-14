# Natural transformations between functors between large categories

```agda
module category-theory.natural-transformations-functors-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-categories
open import category-theory.large-categories

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given [large categories](category-theory.large-categories.md) `C` and `D`, a
**natural transformation** from a
[functor](category-theory.functors-large-categories.md) `F : C → D` to
`G : C → D` consists of :

- a family of morphisms `γ : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (γ x) = (γ y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
coherence-square-Large-Category :
  {αC : Level → Level}
  {βC : Level → Level → Level}
  (C : Large-Category αC βC)
  {l1 l2 l3 l4 : Level}
  {A : obj-Large-Category C l1}
  {B : obj-Large-Category C l2}
  {X : obj-Large-Category C l3}
  {Y : obj-Large-Category C l4}
  (top : hom-Large-Category C A B)
  (left : hom-Large-Category C A X)
  (right : hom-Large-Category C B Y)
  (bottom : hom-Large-Category C X Y) →
  UU (βC l1 l4)
coherence-square-Large-Category C top left right bottom =
  comp-hom-Large-Category C right top ＝
  comp-hom-Large-Category C bottom left

module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Category αC βC}
  {D : Large-Category αD βD}
  (F : functor-Large-Category γF C D)
  (G : functor-Large-Category γG C D)
  where

  hom-family-functor-Large-Category : UUω
  hom-family-functor-Large-Category =
    {l : Level} (X : obj-Large-Category C l) →
    hom-Large-Category D
      ( obj-functor-Large-Category F X)
      ( obj-functor-Large-Category G X)

  record natural-transformation-Large-Category : UUω
    where
    constructor make-natural-transformation
    field
      hom-family-natural-transformation-Large-Category :
        hom-family-functor-Large-Category
      coherence-square-natural-transformation-Large-Category :
        {l1 l2 : Level} {X : obj-Large-Category C l1}
        {Y : obj-Large-Category C l2}
        (f : hom-Large-Category C X Y) →
        coherence-square-Large-Category D
          ( hom-family-natural-transformation-Large-Category X)
          ( hom-functor-Large-Category F f)
          ( hom-functor-Large-Category G f)
          ( hom-family-natural-transformation-Large-Category Y)

  open natural-transformation-Large-Category public
```

## Properties

### The identity natural transformation

Every functor comes equipped with an identity natural transformation.

```agda
module _
  { αC αD γF : Level → Level}
  { βC βD : Level → Level → Level}
  { C : Large-Category αC βC}
  { D : Large-Category αD βD}
  where

  id-natural-transformation-Large-Category :
    ( F : functor-Large-Category γF C D) →
    natural-transformation-Large-Category F F
  hom-family-natural-transformation-Large-Category
    ( id-natural-transformation-Large-Category F) X =
      id-hom-Large-Category D
  coherence-square-natural-transformation-Large-Category
    ( id-natural-transformation-Large-Category F) f =
        ( right-unit-law-comp-hom-Large-Category D
          ( hom-functor-Large-Category F f)) ∙
        ( inv
          ( left-unit-law-comp-hom-Large-Category D
            ( hom-functor-Large-Category F f)))
```

### Composition of natural transformations

```agda
module _
  {αC αD γF γG γH : Level → Level}
  {βC βD : Level → Level → Level}
  {C : Large-Category αC βC}
  {D : Large-Category αD βD}
  (F : functor-Large-Category γF C D)
  (G : functor-Large-Category γG C D)
  (H : functor-Large-Category γH C D)
  where

  comp-natural-transformation-Large-Category :
    natural-transformation-Large-Category G H →
    natural-transformation-Large-Category F G →
    natural-transformation-Large-Category F H
  hom-family-natural-transformation-Large-Category
    ( comp-natural-transformation-Large-Category b a) X =
      comp-hom-Large-Category D
        ( hom-family-natural-transformation-Large-Category b X)
        ( hom-family-natural-transformation-Large-Category a X)
  coherence-square-natural-transformation-Large-Category
    ( comp-natural-transformation-Large-Category b a) {X = X} {Y} f =
    ( inv
      ( associative-comp-hom-Large-Category D
        ( hom-functor-Large-Category H f)
        ( hom-family-natural-transformation-Large-Category b X)
        ( hom-family-natural-transformation-Large-Category a X))) ∙
    ( ap
      ( comp-hom-Large-Category' D
        ( hom-family-natural-transformation-Large-Category a X))
      ( coherence-square-natural-transformation-Large-Category b f)) ∙
    ( associative-comp-hom-Large-Category D
      ( hom-family-natural-transformation-Large-Category b Y)
      ( hom-functor-Large-Category G f)
      ( hom-family-natural-transformation-Large-Category a X)) ∙
    ( ap
      ( comp-hom-Large-Category D
        ( hom-family-natural-transformation-Large-Category b Y))
      ( coherence-square-natural-transformation-Large-Category a f)) ∙
    ( inv
      ( associative-comp-hom-Large-Category D
        ( hom-family-natural-transformation-Large-Category b Y)
        ( hom-family-natural-transformation-Large-Category a Y)
        ( hom-functor-Large-Category F f)))
```

## See also

- [Homotopies of natural transformations in large categories](category-theory.homotopies-natural-transformations-large-categories.md)

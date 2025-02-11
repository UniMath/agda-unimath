# Natural transformations between functors between large categories

```agda
module category-theory.natural-transformations-functors-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-categories
open import category-theory.large-categories
open import category-theory.natural-transformations-functors-large-precategories

open import foundation.universe-levels
```

</details>

## Idea

Given [large categories](category-theory.large-categories.md) `C` and `D`, a
**natural transformation** from a
[functor](category-theory.functors-large-categories.md) `F : C → D` to
`G : C → D` consists of :

- a family of morphisms `γ : (x : C) → hom (F x) (G x)` such that the following
  **naturality condition** holds:
- `(G f) ∘ (γ x) = (γ y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Category αC βC)
  (D : Large-Category αD βD)
  (F : functor-Large-Category γF C D)
  (G : functor-Large-Category γG C D)
  where

  family-of-morphisms-functor-Large-Category : UUω
  family-of-morphisms-functor-Large-Category =
    family-of-morphisms-functor-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  naturality-family-of-morphisms-functor-Large-Category :
    family-of-morphisms-functor-Large-Category → UUω
  naturality-family-of-morphisms-functor-Large-Category =
    naturality-family-of-morphisms-functor-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  natural-transformation-Large-Category : UUω
  natural-transformation-Large-Category =
    natural-transformation-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  hom-natural-transformation-Large-Category :
    natural-transformation-Large-Category →
    family-of-morphisms-functor-Large-Category
  hom-natural-transformation-Large-Category =
    hom-natural-transformation-Large-Precategory

  naturality-natural-transformation-Large-Category :
    (τ : natural-transformation-Large-Category) →
    naturality-family-of-morphisms-functor-Large-Category
      (hom-natural-transformation-Large-Category τ)
  naturality-natural-transformation-Large-Category =
    naturality-natural-transformation-Large-Precategory
```

## Properties

### The identity natural transformation

Every functor comes equipped with an identity natural transformation.

```agda
module _
  { αC αD γF : Level → Level}
  { βC βD : Level → Level → Level}
  ( C : Large-Category αC βC)
  ( D : Large-Category αD βD)
  ( F : functor-Large-Category γF C D)
  where

  hom-id-natural-transformation-Large-Category :
    family-of-morphisms-functor-Large-Category C D F F
  hom-id-natural-transformation-Large-Category =
    hom-id-natural-transformation-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  naturality-id-natural-transformation-Large-Category :
    naturality-family-of-morphisms-functor-Large-Category C D F F
      hom-id-natural-transformation-Large-Category
  naturality-id-natural-transformation-Large-Category =
    naturality-id-natural-transformation-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  id-natural-transformation-Large-Category :
    natural-transformation-Large-Category C D F F
  id-natural-transformation-Large-Category =
    id-natural-transformation-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
```

### Composition of natural transformations

```agda
module _
  {αC αD γF γG γH : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Category αC βC)
  (D : Large-Category αD βD)
  (F : functor-Large-Category γF C D)
  (G : functor-Large-Category γG C D)
  (H : functor-Large-Category γH C D)
  (τ : natural-transformation-Large-Category C D G H)
  (σ : natural-transformation-Large-Category C D F G)
  where

  hom-comp-natural-transformation-Large-Category :
    family-of-morphisms-functor-Large-Category C D F H
  hom-comp-natural-transformation-Large-Category =
    hom-comp-natural-transformation-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)
      ( H)
      ( τ)
      ( σ)

  naturality-comp-natural-transformation-Large-Category :
    naturality-family-of-morphisms-functor-Large-Category C D F H
      hom-comp-natural-transformation-Large-Category
  naturality-comp-natural-transformation-Large-Category =
    naturality-comp-natural-transformation-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)
      ( H)
      ( τ)
      ( σ)

  comp-natural-transformation-Large-Category :
    natural-transformation-Large-Category C D F H
  comp-natural-transformation-Large-Category =
    comp-natural-transformation-Large-Precategory
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)
      ( H)
      ( τ)
      ( σ)
```

# Natural transformations between functors between large precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.natural-transformations-functors-large-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategories funext
open import category-theory.functors-large-precategories funext
open import category-theory.large-precategories funext

open import foundation.action-on-identifications-functions
open import foundation.identity-types funext
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
module _
  {αC αD γF γG : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (F : functor-Large-Precategory γF C D)
  (G : functor-Large-Precategory γG C D)
  where

  family-of-morphisms-functor-Large-Precategory : UUω
  family-of-morphisms-functor-Large-Precategory =
    {l : Level} (X : obj-Large-Precategory C l) →
    hom-Large-Precategory D
      ( obj-functor-Large-Precategory F X)
      ( obj-functor-Large-Precategory G X)

  naturality-family-of-morphisms-functor-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory → UUω
  naturality-family-of-morphisms-functor-Large-Precategory τ =
    {l1 l2 : Level} {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2}
    (f : hom-Large-Precategory C X Y) →
    coherence-square-hom-Large-Precategory D
      ( hom-functor-Large-Precategory F f)
      ( τ X)
      ( τ Y)
      ( hom-functor-Large-Precategory G f)

  record natural-transformation-Large-Precategory : UUω
    where
    constructor make-natural-transformation
    field
      hom-natural-transformation-Large-Precategory :
        family-of-morphisms-functor-Large-Precategory
      naturality-natural-transformation-Large-Precategory :
        naturality-family-of-morphisms-functor-Large-Precategory
          hom-natural-transformation-Large-Precategory

  open natural-transformation-Large-Precategory public
```

## Properties

### The identity natural transformation

Every functor comes equipped with an identity natural transformation.

```agda
module _
  { αC αD γF : Level → Level}
  { βC βD : Level → Level → Level}
  ( C : Large-Precategory αC βC)
  ( D : Large-Precategory αD βD)
  ( F : functor-Large-Precategory γF C D)
  where

  hom-id-natural-transformation-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory C D F F
  hom-id-natural-transformation-Large-Precategory X =
    id-hom-Large-Precategory D

  naturality-id-natural-transformation-Large-Precategory :
    naturality-family-of-morphisms-functor-Large-Precategory C D F F
      hom-id-natural-transformation-Large-Precategory
  naturality-id-natural-transformation-Large-Precategory f =
    ( right-unit-law-comp-hom-Large-Precategory D
        ( hom-functor-Large-Precategory F f)) ∙
    ( inv
      ( left-unit-law-comp-hom-Large-Precategory D
        ( hom-functor-Large-Precategory F f)))

  id-natural-transformation-Large-Precategory :
    natural-transformation-Large-Precategory C D F F
  hom-natural-transformation-Large-Precategory
    id-natural-transformation-Large-Precategory =
    hom-id-natural-transformation-Large-Precategory
  naturality-natural-transformation-Large-Precategory
    id-natural-transformation-Large-Precategory =
    naturality-id-natural-transformation-Large-Precategory
```

### Composition of natural transformations

```agda
module _
  {αC αD γF γG γH : Level → Level}
  {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC)
  (D : Large-Precategory αD βD)
  (F : functor-Large-Precategory γF C D)
  (G : functor-Large-Precategory γG C D)
  (H : functor-Large-Precategory γH C D)
  (τ : natural-transformation-Large-Precategory C D G H)
  (σ : natural-transformation-Large-Precategory C D F G)
  where

  hom-comp-natural-transformation-Large-Precategory :
    family-of-morphisms-functor-Large-Precategory C D F H
  hom-comp-natural-transformation-Large-Precategory X =
    comp-hom-Large-Precategory D
      ( hom-natural-transformation-Large-Precategory τ X)
      ( hom-natural-transformation-Large-Precategory σ X)

  naturality-comp-natural-transformation-Large-Precategory :
    naturality-family-of-morphisms-functor-Large-Precategory C D F H
      hom-comp-natural-transformation-Large-Precategory
  naturality-comp-natural-transformation-Large-Precategory {X = X} {Y} f =
    inv
      ( associative-comp-hom-Large-Precategory D
        ( hom-functor-Large-Precategory H f)
        ( hom-natural-transformation-Large-Precategory τ X)
        ( hom-natural-transformation-Large-Precategory σ X)) ∙
    ( ap
      ( comp-hom-Large-Precategory' D
        ( hom-natural-transformation-Large-Precategory σ X))
      ( naturality-natural-transformation-Large-Precategory τ f)) ∙
    ( associative-comp-hom-Large-Precategory D
      ( hom-natural-transformation-Large-Precategory τ Y)
      ( hom-functor-Large-Precategory G f)
      ( hom-natural-transformation-Large-Precategory σ X)) ∙
    ( ap
      ( comp-hom-Large-Precategory D
        ( hom-natural-transformation-Large-Precategory τ Y))
      ( naturality-natural-transformation-Large-Precategory σ f)) ∙
    ( inv
      (associative-comp-hom-Large-Precategory D
        ( hom-natural-transformation-Large-Precategory τ Y)
        ( hom-natural-transformation-Large-Precategory σ Y)
        ( hom-functor-Large-Precategory F f)))

  comp-natural-transformation-Large-Precategory :
    natural-transformation-Large-Precategory C D F H
  hom-natural-transformation-Large-Precategory
    comp-natural-transformation-Large-Precategory =
    hom-comp-natural-transformation-Large-Precategory
  naturality-natural-transformation-Large-Precategory
    comp-natural-transformation-Large-Precategory =
    naturality-comp-natural-transformation-Large-Precategory
```

## See also

- [Homotopies of natural transformations in large precategories](category-theory.homotopies-natural-transformations-large-precategories.md)

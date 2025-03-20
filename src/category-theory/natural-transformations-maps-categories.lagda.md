# Natural transformations between maps between categories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.natural-transformations-maps-categories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext
open import category-theory.maps-categories funext
open import category-theory.natural-transformations-maps-precategories funext

open import foundation.embeddings funext
open import foundation.equivalences funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.propositions funext
open import foundation.sets funext
open import foundation.universe-levels
```

</details>

## Idea

A **natural transformation** between
[maps between categories](category-theory.maps-categories.md) is a
[natural transformation](category-theory.natural-transformations-maps-precategories.md)
between the [maps](category-theory.maps-precategories.md) on the underlying
[precategories](category-theory.precategories.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  hom-family-map-Category : UU (l1 ⊔ l4)
  hom-family-map-Category =
    hom-family-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  is-natural-transformation-map-Category :
    hom-family-map-Category → UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-map-Category =
    is-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  natural-transformation-map-Category : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-map-Category =
    natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  hom-family-natural-transformation-map-Category :
    natural-transformation-map-Category → hom-family-map-Category
  hom-family-natural-transformation-map-Category =
    hom-family-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  naturality-natural-transformation-map-Category :
    (γ : natural-transformation-map-Category) →
    is-natural-transformation-map-Category
      ( hom-family-natural-transformation-map-Category γ)
  naturality-natural-transformation-map-Category =
    naturality-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Category l1 l2) (D : Category l3 l4)
  where

  id-natural-transformation-map-Category :
    (F : map-Category C D) → natural-transformation-map-Category C D F F
  id-natural-transformation-map-Category =
    id-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  comp-natural-transformation-map-Category :
    (F G H : map-Category C D) →
    natural-transformation-map-Category C D G H →
    natural-transformation-map-Category C D F G →
    natural-transformation-map-Category C D F H
  comp-natural-transformation-map-Category =
    comp-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are
[sets](foundation-core.sets.md).

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  (F G : map-Category C D)
  where

  is-prop-is-natural-transformation-map-Category :
    ( γ : hom-family-map-Category C D F G) →
    is-prop (is-natural-transformation-map-Category C D F G γ)
  is-prop-is-natural-transformation-map-Category =
    is-prop-is-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  is-natural-transformation-prop-map-Category :
    ( γ : hom-family-map-Category C D F G) → Prop (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-prop-map-Category =
    is-natural-transformation-prop-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

### The set of natural transformations

```agda
  is-emb-hom-family-natural-transformation-map-Category :
    is-emb (hom-family-natural-transformation-map-Category C D F G)
  is-emb-hom-family-natural-transformation-map-Category =
    is-emb-hom-family-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  is-set-natural-transformation-map-Category :
    is-set (natural-transformation-map-Category C D F G)
  is-set-natural-transformation-map-Category =
    is-set-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  natural-transformation-map-set-Category : Set (l1 ⊔ l2 ⊔ l4)
  natural-transformation-map-set-Category =
    natural-transformation-map-set-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  extensionality-natural-transformation-map-Category :
    (α β : natural-transformation-map-Category C D F G) →
    ( α ＝ β) ≃
    ( hom-family-natural-transformation-map-Category C D F G α ~
      hom-family-natural-transformation-map-Category C D F G β)
  extensionality-natural-transformation-map-Category =
    extensionality-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)

  eq-htpy-hom-family-natural-transformation-map-Category :
    (α β : natural-transformation-map-Category C D F G) →
    ( hom-family-natural-transformation-map-Category C D F G α ~
      hom-family-natural-transformation-map-Category C D F G β) →
    α ＝ β
  eq-htpy-hom-family-natural-transformation-map-Category =
    eq-htpy-hom-family-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
      ( G)
```

### Categorical laws for natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Category l1 l2) (D : Category l3 l4)
  where

  right-unit-law-comp-natural-transformation-map-Category :
    {F G : map-Category C D}
    (α : natural-transformation-map-Category C D F G) →
    comp-natural-transformation-map-Category C D F F G α
      ( id-natural-transformation-map-Category C D F) ＝ α
  right-unit-law-comp-natural-transformation-map-Category {F} {G} =
    right-unit-law-comp-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      F G

  left-unit-law-comp-natural-transformation-map-Category :
    {F G : map-Category C D}
    (α : natural-transformation-map-Category C D F G) →
    comp-natural-transformation-map-Category C D F G G
      ( id-natural-transformation-map-Category C D G) α ＝ α
  left-unit-law-comp-natural-transformation-map-Category {F} {G} =
    left-unit-law-comp-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      F G

  associative-comp-natural-transformation-map-Category :
    (F G H I : map-Category C D)
    (α : natural-transformation-map-Category C D F G)
    (β : natural-transformation-map-Category C D G H)
    (γ : natural-transformation-map-Category C D H I) →
    comp-natural-transformation-map-Category C D F G I
      ( comp-natural-transformation-map-Category C D G H I γ β) α ＝
    comp-natural-transformation-map-Category C D F H I γ
      ( comp-natural-transformation-map-Category C D F G H β α)
  associative-comp-natural-transformation-map-Category =
    associative-comp-natural-transformation-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
```

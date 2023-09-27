# Natural transformations between functors between precategories

```agda
module category-theory.natural-transformations-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given [precategories](category-theory.precategories.md) `C` and `D`, a **natural
transformation** from a [functor](category-theory.functors-precategories.md)
`F : C → D` to `G : C → D` consists of :

- a family of morphisms `γ : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (γ x) = (γ y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  hom-family-functor-Precategory : UU (l1 ⊔ l4)
  hom-family-functor-Precategory =
    hom-family-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  is-natural-transformation-Precategory :
    hom-family-functor-Precategory → UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-Precategory =
    is-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  natural-transformation-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-Precategory =
    natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  hom-family-natural-transformation-Precategory :
    natural-transformation-Precategory → hom-family-functor-Precategory
  hom-family-natural-transformation-Precategory =
    hom-family-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  coherence-square-natural-transformation-Precategory :
    (γ : natural-transformation-Precategory) →
    is-natural-transformation-Precategory
      ( hom-family-natural-transformation-Precategory γ)
  coherence-square-natural-transformation-Precategory =
    coherence-square-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  id-natural-transformation-Precategory :
    (F : functor-Precategory C D) → natural-transformation-Precategory C D F F
  id-natural-transformation-Precategory F =
    id-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)

  comp-natural-transformation-Precategory :
    (F G H : functor-Precategory C D) →
    natural-transformation-Precategory C D G H →
    natural-transformation-Precategory C D F G →
    natural-transformation-Precategory C D F H
  comp-natural-transformation-Precategory F G H =
    comp-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)
      ( map-functor-Precategory C D H)
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are
[sets](foundation-core.sets.md).

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-prop-is-natural-transformation-Precategory :
    (γ : hom-family-functor-Precategory C D F G) →
    is-prop (is-natural-transformation-Precategory C D F G γ)
  is-prop-is-natural-transformation-Precategory =
    is-prop-is-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  is-natural-transformation-prop-Precategory :
    (γ : hom-family-functor-Precategory C D F G) → Prop (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-prop-Precategory =
    is-natural-transformation-prop-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)
```

### The set of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-emb-hom-family-natural-transformation-Precategory :
    is-emb (hom-family-natural-transformation-Precategory C D F G)
  is-emb-hom-family-natural-transformation-Precategory =
    is-emb-hom-family-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  emb-hom-family-natural-transformation-Precategory :
    natural-transformation-Precategory C D F G ↪
    hom-family-functor-Precategory C D F G
  emb-hom-family-natural-transformation-Precategory =
    emb-hom-family-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  is-set-natural-transformation-Precategory :
    is-set (natural-transformation-Precategory C D F G)
  is-set-natural-transformation-Precategory =
    is-set-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  natural-transformation-set-Precategory :
    Set (l1 ⊔ l2 ⊔ l4)
  pr1 (natural-transformation-set-Precategory) =
    natural-transformation-Precategory C D F G
  pr2 (natural-transformation-set-Precategory) =
    is-set-natural-transformation-Precategory

  extensionality-natural-transformation-Precategory :
    (α β : natural-transformation-Precategory C D F G) →
    ( α ＝ β) ≃
    ( hom-family-natural-transformation-Precategory C D F G α ~
      hom-family-natural-transformation-Precategory C D F G β)
  extensionality-natural-transformation-Precategory =
    extensionality-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  eq-htpy-hom-family-natural-transformation-Precategory :
    (α β : natural-transformation-Precategory C D F G) →
    ( hom-family-natural-transformation-Precategory C D F G α ~
      hom-family-natural-transformation-Precategory C D F G β) →
    α ＝ β
  eq-htpy-hom-family-natural-transformation-Precategory =
    eq-htpy-hom-family-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)
```

### Categorical laws for natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  right-unit-law-comp-natural-transformation-Precategory :
    (F G : functor-Precategory C D)
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F F G α
      ( id-natural-transformation-Precategory C D F) ＝ α
  right-unit-law-comp-natural-transformation-Precategory F G =
    right-unit-law-comp-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  left-unit-law-comp-natural-transformation-Precategory :
    (F G : functor-Precategory C D)
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F G G
      ( id-natural-transformation-Precategory C D G) α ＝ α
  left-unit-law-comp-natural-transformation-Precategory F G =
    left-unit-law-comp-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  associative-comp-natural-transformation-Precategory :
    (F G H I : functor-Precategory C D)
    (α : natural-transformation-Precategory C D F G)
    (β : natural-transformation-Precategory C D G H)
    (γ : natural-transformation-Precategory C D H I) →
    comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I γ β) α ＝
    comp-natural-transformation-Precategory C D F H I γ
      ( comp-natural-transformation-Precategory C D F G H β α)
  associative-comp-natural-transformation-Precategory F G H I =
    associative-comp-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)
      ( map-functor-Precategory C D H)
      ( map-functor-Precategory C D I)
```

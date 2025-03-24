# Natural transformations between functors from small to large categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.natural-transformations-functors-from-small-to-large-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext univalence truncations
open import category-theory.functors-from-small-to-large-categories funext univalence truncations
open import category-theory.large-categories funext univalence truncations
open import category-theory.natural-transformations-functors-from-small-to-large-precategories funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.embeddings funext
open import foundation.equivalences funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels
```

</details>

## Idea

Given a small [category](category-theory.categories.md) `C` and a
[large category](category-theory.large-categories.md) `D`, a **natural
transformation** from a
[functor](category-theory.functors-from-small-to-large-categories.md)
`F : C → D` to `G : C → D` consists of :

- a family of morphisms `a : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (a x) = (a y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  (F : functor-Small-Large-Category C D γF)
  (G : functor-Small-Large-Category C D γG)
  where

  hom-family-functor-Small-Large-Category : UU (l1 ⊔ β γF γG)
  hom-family-functor-Small-Large-Category =
    hom-family-functor-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  is-natural-transformation-Small-Large-Category :
    hom-family-functor-Small-Large-Category → UU (l1 ⊔ l2 ⊔ β γF γG)
  is-natural-transformation-Small-Large-Category =
    is-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  natural-transformation-Small-Large-Category : UU (l1 ⊔ l2 ⊔ β γF γG)
  natural-transformation-Small-Large-Category =
    natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  hom-natural-transformation-Small-Large-Category :
    natural-transformation-Small-Large-Category →
    hom-family-functor-Small-Large-Category
  hom-natural-transformation-Small-Large-Category =
    hom-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  naturality-natural-transformation-Small-Large-Category :
    (γ : natural-transformation-Small-Large-Category) →
    is-natural-transformation-Small-Large-Category
      ( hom-natural-transformation-Small-Large-Category γ)
  naturality-natural-transformation-Small-Large-Category =
    naturality-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  where

  id-natural-transformation-Small-Large-Category :
    {γF : Level} (F : functor-Small-Large-Category C D γF) →
    natural-transformation-Small-Large-Category C D F F
  id-natural-transformation-Small-Large-Category =
    id-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D)

  comp-natural-transformation-Small-Large-Category :
    {γF γG γH : Level}
    (F : functor-Small-Large-Category C D γF)
    (G : functor-Small-Large-Category C D γG)
    (H : functor-Small-Large-Category C D γH) →
    natural-transformation-Small-Large-Category C D G H →
    natural-transformation-Small-Large-Category C D F G →
    natural-transformation-Small-Large-Category C D F H
  comp-natural-transformation-Small-Large-Category =
    comp-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D)
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are
[sets](foundation-core.sets.md).

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  (F : functor-Small-Large-Category C D γF)
  (G : functor-Small-Large-Category C D γG)
  where

  is-prop-is-natural-transformation-Small-Large-Category :
    (γ : hom-family-functor-Small-Large-Category C D F G) →
    is-prop (is-natural-transformation-Small-Large-Category C D F G γ)
  is-prop-is-natural-transformation-Small-Large-Category =
    is-prop-is-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  is-natural-transformation-prop-Small-Large-Category :
    (γ : hom-family-functor-Small-Large-Category C D F G) →
    Prop (l1 ⊔ l2 ⊔ β γF γG)
  is-natural-transformation-prop-Small-Large-Category =
    is-natural-transformation-prop-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G
```

### The set of natural transformations

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  (F : functor-Small-Large-Category C D γF)
  (G : functor-Small-Large-Category C D γG)
  where

  is-emb-hom-natural-transformation-Small-Large-Category :
    is-emb (hom-natural-transformation-Small-Large-Category C D F G)
  is-emb-hom-natural-transformation-Small-Large-Category =
    is-emb-hom-family-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  emb-hom-natural-transformation-Small-Large-Category :
    natural-transformation-Small-Large-Category C D F G ↪
    hom-family-functor-Small-Large-Category C D F G
  emb-hom-natural-transformation-Small-Large-Category =
    emb-hom-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  is-set-natural-transformation-Small-Large-Category :
    is-set (natural-transformation-Small-Large-Category C D F G)
  is-set-natural-transformation-Small-Large-Category =
    is-set-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  natural-transformation-set-Small-Large-Category :
    Set (l1 ⊔ l2 ⊔ β γF γG)
  pr1 (natural-transformation-set-Small-Large-Category) =
    natural-transformation-Small-Large-Category C D F G
  pr2 (natural-transformation-set-Small-Large-Category) =
    is-set-natural-transformation-Small-Large-Category

  extensionality-natural-transformation-Small-Large-Category :
    (a b : natural-transformation-Small-Large-Category C D F G) →
    ( a ＝ b) ≃
    ( hom-natural-transformation-Small-Large-Category C D F G a ~
      hom-natural-transformation-Small-Large-Category C D F G b)
  extensionality-natural-transformation-Small-Large-Category =
    extensionality-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G

  eq-htpy-hom-natural-transformation-Small-Large-Category :
    (a b : natural-transformation-Small-Large-Category C D F G) →
    ( hom-natural-transformation-Small-Large-Category C D F G a ~
      hom-natural-transformation-Small-Large-Category C D F G b) →
    a ＝ b
  eq-htpy-hom-natural-transformation-Small-Large-Category =
    eq-htpy-hom-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D) F G
```

### Categorical laws for natural transformations

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  where

  right-unit-law-comp-natural-transformation-Small-Large-Category :
    {γF γG : Level}
    (F : functor-Small-Large-Category C D γF)
    (G : functor-Small-Large-Category C D γG)
    (a : natural-transformation-Small-Large-Category C D F G) →
    comp-natural-transformation-Small-Large-Category C D F F G a
      ( id-natural-transformation-Small-Large-Category C D F) ＝ a
  right-unit-law-comp-natural-transformation-Small-Large-Category =
    right-unit-law-comp-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D)

  left-unit-law-comp-natural-transformation-Small-Large-Category :
    {γF γG : Level}
    (F : functor-Small-Large-Category C D γF)
    (G : functor-Small-Large-Category C D γG)
    (a : natural-transformation-Small-Large-Category C D F G) →
    comp-natural-transformation-Small-Large-Category C D F G G
      ( id-natural-transformation-Small-Large-Category C D G) a ＝ a
  left-unit-law-comp-natural-transformation-Small-Large-Category =
    left-unit-law-comp-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D)

  associative-comp-natural-transformation-Small-Large-Category :
    {γF γG γH γI : Level}
    (F : functor-Small-Large-Category C D γF)
    (G : functor-Small-Large-Category C D γG)
    (H : functor-Small-Large-Category C D γH)
    (I : functor-Small-Large-Category C D γI)
    (a : natural-transformation-Small-Large-Category C D F G)
    (b : natural-transformation-Small-Large-Category C D G H)
    (c : natural-transformation-Small-Large-Category C D H I) →
    comp-natural-transformation-Small-Large-Category C D F G I
      ( comp-natural-transformation-Small-Large-Category C D G H I c b) a ＝
    comp-natural-transformation-Small-Large-Category C D F H I c
      ( comp-natural-transformation-Small-Large-Category C D F G H b a)
  associative-comp-natural-transformation-Small-Large-Category =
    associative-comp-natural-transformation-Small-Large-Precategory
      ( precategory-Category C) (large-precategory-Large-Category D)
```

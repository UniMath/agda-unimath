# Natural transformations between functors from small to large precategories

```agda
module category-theory.natural-transformations-functors-from-small-to-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-maps-from-small-to-large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.embeddings
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

Given a small [precategory](category-theory.precategories.md) `C` and a
[large precategory](category-theory.large-precategories.md) `D`, a **natural
transformation** from a
[functor](category-theory.functors-from-small-to-large-precategories.md)
`F : C → D` to `G : C → D` consists of :

- a family of morphisms `a : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (a x) = (a y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (F : functor-Small-Large-Precategory C D γF)
  (G : functor-Small-Large-Precategory C D γG)
  where

  hom-family-functor-Small-Large-Precategory : UU (l1 ⊔ β γF γG)
  hom-family-functor-Small-Large-Precategory =
    hom-family-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  is-natural-transformation-Small-Large-Precategory :
    hom-family-functor-Small-Large-Precategory → UU (l1 ⊔ l2 ⊔ β γF γG)
  is-natural-transformation-Small-Large-Precategory =
    is-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  natural-transformation-Small-Large-Precategory : UU (l1 ⊔ l2 ⊔ β γF γG)
  natural-transformation-Small-Large-Precategory =
    natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  hom-natural-transformation-Small-Large-Precategory :
    natural-transformation-Small-Large-Precategory →
    hom-family-functor-Small-Large-Precategory
  hom-natural-transformation-Small-Large-Precategory =
    hom-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  naturality-natural-transformation-Small-Large-Precategory :
    (γ : natural-transformation-Small-Large-Precategory) →
    is-natural-transformation-Small-Large-Precategory
      ( hom-natural-transformation-Small-Large-Precategory γ)
  naturality-natural-transformation-Small-Large-Precategory =
    naturality-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  id-natural-transformation-Small-Large-Precategory :
    {γF : Level} (F : functor-Small-Large-Precategory C D γF) →
    natural-transformation-Small-Large-Precategory C D F F
  id-natural-transformation-Small-Large-Precategory F =
    id-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)

  comp-natural-transformation-Small-Large-Precategory :
    {γF γG γH : Level}
    (F : functor-Small-Large-Precategory C D γF)
    (G : functor-Small-Large-Precategory C D γG)
    (H : functor-Small-Large-Precategory C D γH) →
    natural-transformation-Small-Large-Precategory C D G H →
    natural-transformation-Small-Large-Precategory C D F G →
    natural-transformation-Small-Large-Precategory C D F H
  comp-natural-transformation-Small-Large-Precategory F G H =
    comp-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)
      ( map-functor-Small-Large-Precategory C D H)
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are
[sets](foundation-core.sets.md).

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (F : functor-Small-Large-Precategory C D γF)
  (G : functor-Small-Large-Precategory C D γG)
  where

  is-prop-is-natural-transformation-Small-Large-Precategory :
    (γ : hom-family-functor-Small-Large-Precategory C D F G) →
    is-prop (is-natural-transformation-Small-Large-Precategory C D F G γ)
  is-prop-is-natural-transformation-Small-Large-Precategory =
    is-prop-is-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  is-natural-transformation-prop-Small-Large-Precategory :
    (γ : hom-family-functor-Small-Large-Precategory C D F G) →
    Prop (l1 ⊔ l2 ⊔ β γF γG)
  is-natural-transformation-prop-Small-Large-Precategory =
    is-natural-transformation-prop-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)
```

### The set of natural transformations

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (F : functor-Small-Large-Precategory C D γF)
  (G : functor-Small-Large-Precategory C D γG)
  where

  is-emb-hom-family-natural-transformation-Small-Large-Precategory :
    is-emb (hom-natural-transformation-Small-Large-Precategory C D F G)
  is-emb-hom-family-natural-transformation-Small-Large-Precategory =
    is-emb-hom-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  emb-hom-natural-transformation-Small-Large-Precategory :
    natural-transformation-Small-Large-Precategory C D F G ↪
    hom-family-functor-Small-Large-Precategory C D F G
  emb-hom-natural-transformation-Small-Large-Precategory =
    emb-hom-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  is-set-natural-transformation-Small-Large-Precategory :
    is-set (natural-transformation-Small-Large-Precategory C D F G)
  is-set-natural-transformation-Small-Large-Precategory =
    is-set-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  natural-transformation-set-Small-Large-Precategory :
    Set (l1 ⊔ l2 ⊔ β γF γG)
  pr1 (natural-transformation-set-Small-Large-Precategory) =
    natural-transformation-Small-Large-Precategory C D F G
  pr2 (natural-transformation-set-Small-Large-Precategory) =
    is-set-natural-transformation-Small-Large-Precategory

  extensionality-natural-transformation-Small-Large-Precategory :
    (a b : natural-transformation-Small-Large-Precategory C D F G) →
    ( a ＝ b) ≃
    ( hom-natural-transformation-Small-Large-Precategory C D F G a ~
      hom-natural-transformation-Small-Large-Precategory C D F G b)
  extensionality-natural-transformation-Small-Large-Precategory =
    extensionality-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  eq-htpy-hom-natural-transformation-Small-Large-Precategory :
    (a b : natural-transformation-Small-Large-Precategory C D F G) →
    ( hom-natural-transformation-Small-Large-Precategory C D F G a ~
      hom-natural-transformation-Small-Large-Precategory C D F G b) →
    a ＝ b
  eq-htpy-hom-natural-transformation-Small-Large-Precategory =
    eq-htpy-hom-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)
```

### Categorical laws for natural transformations

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  right-unit-law-comp-natural-transformation-Small-Large-Precategory :
    {γF γG : Level}
    (F : functor-Small-Large-Precategory C D γF)
    (G : functor-Small-Large-Precategory C D γG)
    (a : natural-transformation-Small-Large-Precategory C D F G) →
    comp-natural-transformation-Small-Large-Precategory C D F F G a
      ( id-natural-transformation-Small-Large-Precategory C D F) ＝ a
  right-unit-law-comp-natural-transformation-Small-Large-Precategory F G =
    right-unit-law-comp-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  left-unit-law-comp-natural-transformation-Small-Large-Precategory :
    {γF γG : Level}
    (F : functor-Small-Large-Precategory C D γF)
    (G : functor-Small-Large-Precategory C D γG)
    (a : natural-transformation-Small-Large-Precategory C D F G) →
    comp-natural-transformation-Small-Large-Precategory C D F G G
      ( id-natural-transformation-Small-Large-Precategory C D G) a ＝ a
  left-unit-law-comp-natural-transformation-Small-Large-Precategory F G =
    left-unit-law-comp-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  associative-comp-natural-transformation-Small-Large-Precategory :
    {γF γG γH γI : Level}
    (F : functor-Small-Large-Precategory C D γF)
    (G : functor-Small-Large-Precategory C D γG)
    (H : functor-Small-Large-Precategory C D γH)
    (I : functor-Small-Large-Precategory C D γI)
    (a : natural-transformation-Small-Large-Precategory C D F G)
    (b : natural-transformation-Small-Large-Precategory C D G H)
    (c : natural-transformation-Small-Large-Precategory C D H I) →
    comp-natural-transformation-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-Small-Large-Precategory C D G H I c b) a ＝
    comp-natural-transformation-Small-Large-Precategory C D F H I c
      ( comp-natural-transformation-Small-Large-Precategory C D F G H b a)
  associative-comp-natural-transformation-Small-Large-Precategory F G H I =
    associative-comp-natural-transformation-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)
      ( map-functor-Small-Large-Precategory C D H)
      ( map-functor-Small-Large-Precategory C D I)

  involutive-eq-associative-comp-natural-transformation-Small-Large-Precategory :
    {γF γG γH γI : Level}
    (F : functor-Small-Large-Precategory C D γF)
    (G : functor-Small-Large-Precategory C D γG)
    (H : functor-Small-Large-Precategory C D γH)
    (I : functor-Small-Large-Precategory C D γI)
    (a : natural-transformation-Small-Large-Precategory C D F G)
    (b : natural-transformation-Small-Large-Precategory C D G H)
    (c : natural-transformation-Small-Large-Precategory C D H I) →
    comp-natural-transformation-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-Small-Large-Precategory C D G H I c b) a ＝ⁱ
    comp-natural-transformation-Small-Large-Precategory C D F H I c
      ( comp-natural-transformation-Small-Large-Precategory C D F G H b a)
  involutive-eq-associative-comp-natural-transformation-Small-Large-Precategory
    F G H I =
    involutive-eq-associative-comp-natural-transformation-map-Small-Large-Precategory
      ( C)
      ( D)
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)
      ( map-functor-Small-Large-Precategory C D H)
      ( map-functor-Small-Large-Precategory C D I)
```

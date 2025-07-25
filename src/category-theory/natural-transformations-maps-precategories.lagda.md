# Natural transformations between maps between precategories

```agda
module category-theory.natural-transformations-maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given [precategories](category-theory.precategories.md) `C` and `D`, a **natural
transformation** from a
[map of precategories](category-theory.maps-precategories.md) `F : C → D` to
`G : C → D` consists of :

- a family of morphisms `γ : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (γ x) = (γ y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  hom-family-map-Precategory : UU (l1 ⊔ l4)
  hom-family-map-Precategory =
    (x : obj-Precategory C) →
    hom-Precategory D
      ( obj-map-Precategory C D F x)
      ( obj-map-Precategory C D G x)

  naturality-hom-family-map-Precategory :
    hom-family-map-Precategory →
    {x y : obj-Precategory C} (f : hom-Precategory C x y) → UU l4
  naturality-hom-family-map-Precategory γ {x} {y} f =
    coherence-square-hom-Precategory D
      ( hom-map-Precategory C D F f)
      ( γ x)
      ( γ y)
      ( hom-map-Precategory C D G f)

  is-natural-transformation-map-Precategory :
    hom-family-map-Precategory → UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-map-Precategory γ =
    {x y : obj-Precategory C} (f : hom-Precategory C x y) →
    naturality-hom-family-map-Precategory γ f

  natural-transformation-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-map-Precategory =
    Σ ( hom-family-map-Precategory)
      ( is-natural-transformation-map-Precategory)

  hom-family-natural-transformation-map-Precategory :
    natural-transformation-map-Precategory → hom-family-map-Precategory
  hom-family-natural-transformation-map-Precategory = pr1

  naturality-natural-transformation-map-Precategory :
    (γ : natural-transformation-map-Precategory) →
    is-natural-transformation-map-Precategory
      ( hom-family-natural-transformation-map-Precategory γ)
  naturality-natural-transformation-map-Precategory = pr2
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  id-natural-transformation-map-Precategory :
    (F : map-Precategory C D) → natural-transformation-map-Precategory C D F F
  pr1 (id-natural-transformation-map-Precategory F) x = id-hom-Precategory D
  pr2 (id-natural-transformation-map-Precategory F) f =
    ( right-unit-law-comp-hom-Precategory D
      ( hom-map-Precategory C D F f)) ∙
    ( inv
      ( left-unit-law-comp-hom-Precategory D
        ( hom-map-Precategory C D F f)))

  comp-natural-transformation-map-Precategory :
    (F G H : map-Precategory C D) →
    natural-transformation-map-Precategory C D G H →
    natural-transformation-map-Precategory C D F G →
    natural-transformation-map-Precategory C D F H
  pr1 (comp-natural-transformation-map-Precategory F G H β α) x =
    comp-hom-Precategory D
      ( hom-family-natural-transformation-map-Precategory C D G H β x)
      ( hom-family-natural-transformation-map-Precategory C D F G α x)
  pr2 (comp-natural-transformation-map-Precategory F G H β α) {X} {Y} f =
    ( inv
      ( associative-comp-hom-Precategory D
        ( hom-map-Precategory C D H f)
        ( hom-family-natural-transformation-map-Precategory C D G H β X)
        ( hom-family-natural-transformation-map-Precategory C D F G α X))) ∙
    ( ap
      ( comp-hom-Precategory' D
        ( hom-family-natural-transformation-map-Precategory C D F G α X))
      ( naturality-natural-transformation-map-Precategory C D G H β f)) ∙
    ( associative-comp-hom-Precategory D
      ( hom-family-natural-transformation-map-Precategory C D G H β Y)
      ( hom-map-Precategory C D G f)
      ( hom-family-natural-transformation-map-Precategory C D F G α X)) ∙
    ( ap
      ( comp-hom-Precategory D
        ( hom-family-natural-transformation-map-Precategory C D G H β Y))
      ( naturality-natural-transformation-map-Precategory C D F G α f)) ∙
    ( inv
      ( associative-comp-hom-Precategory D
        ( hom-family-natural-transformation-map-Precategory C D G H β Y)
        ( hom-family-natural-transformation-map-Precategory C D F G α Y)
        ( hom-map-Precategory C D F f)))
```

## Equality of functors induces a natural transformation

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  natural-transformation-map-eq-Precategory :
    (F G : map-Precategory C D) →
    F ＝ G →
    natural-transformation-map-Precategory C D F G
  natural-transformation-map-eq-Precategory F G refl =
    id-natural-transformation-map-Precategory C D F

  natural-transformation-map-eq-inv-Precategory :
    (F G : map-Precategory C D) →
    F ＝ G →
    natural-transformation-map-Precategory C D G F
  natural-transformation-map-eq-inv-Precategory F G =
    natural-transformation-map-eq-Precategory G F ∘ inv
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
  (F G : map-Precategory C D)
  where

  is-prop-is-natural-transformation-map-Precategory :
    ( γ : hom-family-map-Precategory C D F G) →
    is-prop (is-natural-transformation-map-Precategory C D F G γ)
  is-prop-is-natural-transformation-map-Precategory γ =
    is-prop-implicit-Π
      ( λ x →
        is-prop-implicit-Π
          ( λ y →
            is-prop-Π
              ( λ f →
                is-set-hom-Precategory D
                  ( obj-map-Precategory C D F x)
                  ( obj-map-Precategory C D G y)
                  ( comp-hom-Precategory D
                    ( hom-map-Precategory C D G f)
                    ( γ x))
                  ( comp-hom-Precategory D
                    ( γ y)
                    ( hom-map-Precategory C D F f)))))

  is-natural-transformation-prop-map-Precategory :
    ( γ : hom-family-map-Precategory C D F G) → Prop (l1 ⊔ l2 ⊔ l4)
  pr1 (is-natural-transformation-prop-map-Precategory α) =
    is-natural-transformation-map-Precategory C D F G α
  pr2 (is-natural-transformation-prop-map-Precategory α) =
    is-prop-is-natural-transformation-map-Precategory α
```

### The set of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : map-Precategory C D)
  where

  is-emb-hom-family-natural-transformation-map-Precategory :
    is-emb (hom-family-natural-transformation-map-Precategory C D F G)
  is-emb-hom-family-natural-transformation-map-Precategory =
    is-emb-inclusion-subtype
      ( is-natural-transformation-prop-map-Precategory C D F G)

  emb-hom-family-natural-transformation-map-Precategory :
    natural-transformation-map-Precategory C D F G ↪
    hom-family-map-Precategory C D F G
  emb-hom-family-natural-transformation-map-Precategory =
    emb-subtype (is-natural-transformation-prop-map-Precategory C D F G)

  is-set-natural-transformation-map-Precategory :
    is-set (natural-transformation-map-Precategory C D F G)
  is-set-natural-transformation-map-Precategory =
    is-set-Σ
      ( is-set-Π
        ( λ x →
          is-set-hom-Precategory D
            ( obj-map-Precategory C D F x)
            ( obj-map-Precategory C D G x)))
      ( λ α →
        is-set-type-Set
          ( set-Prop
            ( is-natural-transformation-prop-map-Precategory C D F G α)))

  natural-transformation-map-set-Precategory :
    Set (l1 ⊔ l2 ⊔ l4)
  pr1 (natural-transformation-map-set-Precategory) =
    natural-transformation-map-Precategory C D F G
  pr2 (natural-transformation-map-set-Precategory) =
    is-set-natural-transformation-map-Precategory

  extensionality-natural-transformation-map-Precategory :
    (α β : natural-transformation-map-Precategory C D F G) →
    ( α ＝ β) ≃
    ( hom-family-natural-transformation-map-Precategory C D F G α ~
      hom-family-natural-transformation-map-Precategory C D F G β)
  extensionality-natural-transformation-map-Precategory α β =
    ( equiv-funext) ∘e
    ( equiv-ap-emb emb-hom-family-natural-transformation-map-Precategory)

  eq-htpy-hom-family-natural-transformation-map-Precategory :
    (α β : natural-transformation-map-Precategory C D F G) →
    ( hom-family-natural-transformation-map-Precategory C D F G α ~
      hom-family-natural-transformation-map-Precategory C D F G β) →
    α ＝ β
  eq-htpy-hom-family-natural-transformation-map-Precategory α β =
    map-inv-equiv (extensionality-natural-transformation-map-Precategory α β)

  htpy-eq-hom-family-natural-transformation-map-Precategory :
    {α β : natural-transformation-map-Precategory C D F G} →
    α ＝ β →
    hom-family-natural-transformation-map-Precategory C D F G α ~
    hom-family-natural-transformation-map-Precategory C D F G β
  htpy-eq-hom-family-natural-transformation-map-Precategory {α} {β} =
    map-equiv (extensionality-natural-transformation-map-Precategory α β)
```

### Categorical laws for natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  right-unit-law-comp-natural-transformation-map-Precategory :
    (F G : map-Precategory C D)
    (α : natural-transformation-map-Precategory C D F G) →
    comp-natural-transformation-map-Precategory C D F F G α
      ( id-natural-transformation-map-Precategory C D F) ＝ α
  right-unit-law-comp-natural-transformation-map-Precategory F G α =
    eq-htpy-hom-family-natural-transformation-map-Precategory C D F G
      ( comp-natural-transformation-map-Precategory C D F F G α
        ( id-natural-transformation-map-Precategory C D F))
      ( α)
      ( right-unit-law-comp-hom-Precategory D ∘
        hom-family-natural-transformation-map-Precategory C D F G α)

  left-unit-law-comp-natural-transformation-map-Precategory :
    (F G : map-Precategory C D)
    (α : natural-transformation-map-Precategory C D F G) →
    comp-natural-transformation-map-Precategory C D F G G
      ( id-natural-transformation-map-Precategory C D G) α ＝ α
  left-unit-law-comp-natural-transformation-map-Precategory F G α =
    eq-htpy-hom-family-natural-transformation-map-Precategory C D F G
      ( comp-natural-transformation-map-Precategory C D F G G
        ( id-natural-transformation-map-Precategory C D G) α)
      ( α)
      ( left-unit-law-comp-hom-Precategory D ∘
        hom-family-natural-transformation-map-Precategory C D F G α)

  associative-comp-natural-transformation-map-Precategory :
    (F G H I : map-Precategory C D)
    (α : natural-transformation-map-Precategory C D F G)
    (β : natural-transformation-map-Precategory C D G H)
    (γ : natural-transformation-map-Precategory C D H I) →
    comp-natural-transformation-map-Precategory C D F G I
      ( comp-natural-transformation-map-Precategory C D G H I γ β) α ＝
    comp-natural-transformation-map-Precategory C D F H I γ
      ( comp-natural-transformation-map-Precategory C D F G H β α)
  associative-comp-natural-transformation-map-Precategory F G H I α β γ =
    eq-htpy-hom-family-natural-transformation-map-Precategory C D F I _ _
    ( λ x →
      associative-comp-hom-Precategory D
        ( hom-family-natural-transformation-map-Precategory C D H I γ x)
        ( hom-family-natural-transformation-map-Precategory C D G H β x)
        ( hom-family-natural-transformation-map-Precategory C D F G α x))

  involutive-eq-associative-comp-natural-transformation-map-Precategory :
    (F G H I : map-Precategory C D)
    (α : natural-transformation-map-Precategory C D F G)
    (β : natural-transformation-map-Precategory C D G H)
    (γ : natural-transformation-map-Precategory C D H I) →
    comp-natural-transformation-map-Precategory C D F G I
      ( comp-natural-transformation-map-Precategory C D G H I γ β) α ＝ⁱ
    comp-natural-transformation-map-Precategory C D F H I γ
      ( comp-natural-transformation-map-Precategory C D F G H β α)
  involutive-eq-associative-comp-natural-transformation-map-Precategory
    F G H I α β γ =
    involutive-eq-eq
      ( associative-comp-natural-transformation-map-Precategory F G H I α β γ)
```

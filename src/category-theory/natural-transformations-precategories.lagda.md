# Natural transformations between functors between precategories

```agda
module category-theory.natural-transformations-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
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
    (x : obj-Precategory C) →
    hom-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D G x)

  is-natural-transformation-Precategory :
    hom-family-functor-Precategory → UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-Precategory γ =
    {x y : obj-Precategory C} (f : hom-Precategory C x y) →
    ( comp-hom-Precategory D (hom-functor-Precategory C D G f) (γ x)) ＝
    ( comp-hom-Precategory D (γ y) (hom-functor-Precategory C D F f))

  natural-transformation-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-Precategory =
    Σ ( hom-family-functor-Precategory)
      ( is-natural-transformation-Precategory)

  hom-family-natural-transformation-Precategory :
    natural-transformation-Precategory → hom-family-functor-Precategory
  hom-family-natural-transformation-Precategory = pr1

  coherence-square-natural-transformation-Precategory :
    (γ : natural-transformation-Precategory) →
    is-natural-transformation-Precategory
      ( hom-family-natural-transformation-Precategory γ)
  coherence-square-natural-transformation-Precategory = pr2
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
  pr1 (id-natural-transformation-Precategory F) x = id-hom-Precategory D
  pr2 (id-natural-transformation-Precategory F) f =
    ( right-unit-law-comp-hom-Precategory D
      ( hom-functor-Precategory C D F f)) ∙
    ( inv
      ( left-unit-law-comp-hom-Precategory D
        ( hom-functor-Precategory C D F f)))

  comp-natural-transformation-Precategory :
    (F G H : functor-Precategory C D) →
    natural-transformation-Precategory C D G H →
    natural-transformation-Precategory C D F G →
    natural-transformation-Precategory C D F H
  pr1 (comp-natural-transformation-Precategory F G H β α) x =
    comp-hom-Precategory D
      ( hom-family-natural-transformation-Precategory C D G H β x)
      ( hom-family-natural-transformation-Precategory C D F G α x)
  pr2 (comp-natural-transformation-Precategory F G H β α) {X} {Y} f =
    ( inv
      ( associative-comp-hom-Precategory D
        ( hom-functor-Precategory C D H f)
        ( hom-family-natural-transformation-Precategory C D G H β X)
        ( hom-family-natural-transformation-Precategory C D F G α X))) ∙
    ( ap
      ( comp-hom-Precategory' D
        ( hom-family-natural-transformation-Precategory C D F G α X))
      ( coherence-square-natural-transformation-Precategory C D G H β f)) ∙
    ( associative-comp-hom-Precategory D
      ( hom-family-natural-transformation-Precategory C D G H β Y)
      ( hom-functor-Precategory C D G f)
      ( hom-family-natural-transformation-Precategory C D F G α X)) ∙
    ( ap
      ( comp-hom-Precategory D
        ( hom-family-natural-transformation-Precategory C D G H β Y))
      ( coherence-square-natural-transformation-Precategory C D F G α f)) ∙
    ( inv
      ( associative-comp-hom-Precategory D
        ( hom-family-natural-transformation-Precategory C D G H β Y)
        ( hom-family-natural-transformation-Precategory C D F G α Y)
        ( hom-functor-Precategory C D F f)))
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
    ( γ : hom-family-functor-Precategory C D F G) →
    is-prop (is-natural-transformation-Precategory C D F G γ)
  is-prop-is-natural-transformation-Precategory γ =
    is-prop-Π'
      ( λ x →
        is-prop-Π'
          ( λ y →
            is-prop-Π
              ( λ f →
                is-set-hom-Precategory D
                  ( obj-functor-Precategory C D F x)
                  ( obj-functor-Precategory C D G y)
                  ( comp-hom-Precategory D
                    ( hom-functor-Precategory C D G f)
                    ( γ x))
                  ( comp-hom-Precategory D
                    ( γ y)
                    ( hom-functor-Precategory C D F f)))))

  is-natural-transformation-Precategory-Prop :
    ( γ : hom-family-functor-Precategory C D F G) → Prop (l1 ⊔ l2 ⊔ l4)
  pr1 (is-natural-transformation-Precategory-Prop α) =
    is-natural-transformation-Precategory C D F G α
  pr2 (is-natural-transformation-Precategory-Prop α) =
    is-prop-is-natural-transformation-Precategory α
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
    is-emb-inclusion-subtype
      ( is-natural-transformation-Precategory-Prop C D F G)

  emb-hom-family-natural-transformation-Precategory :
    natural-transformation-Precategory C D F G ↪
    hom-family-functor-Precategory C D F G
  emb-hom-family-natural-transformation-Precategory =
    emb-subtype (is-natural-transformation-Precategory-Prop C D F G)

  is-set-natural-transformation-Precategory :
    is-set (natural-transformation-Precategory C D F G)
  is-set-natural-transformation-Precategory =
    is-set-Σ
      ( is-set-Π
        ( λ x →
          is-set-hom-Precategory D
            ( obj-functor-Precategory C D F x)
            ( obj-functor-Precategory C D G x)))
      ( λ α →
        is-set-type-Set
          ( set-Prop (is-natural-transformation-Precategory-Prop C D F G α)))

  natural-transformation-Precategory-Set :
    Set (l1 ⊔ l2 ⊔ l4)
  pr1 (natural-transformation-Precategory-Set) =
    natural-transformation-Precategory C D F G
  pr2 (natural-transformation-Precategory-Set) =
    is-set-natural-transformation-Precategory

  extensionality-natural-transformation-Precategory :
    (α β : natural-transformation-Precategory C D F G) →
    ( α ＝ β) ≃
    ( hom-family-natural-transformation-Precategory C D F G α ~
      hom-family-natural-transformation-Precategory C D F G β)
  extensionality-natural-transformation-Precategory α β =
    ( equiv-funext) ∘e
    ( equiv-ap-emb emb-hom-family-natural-transformation-Precategory)

  eq-htpy-hom-family-natural-transformation-Precategory :
    (α β : natural-transformation-Precategory C D F G) →
    ( hom-family-natural-transformation-Precategory C D F G α ~
      hom-family-natural-transformation-Precategory C D F G β) →
    α ＝ β
  eq-htpy-hom-family-natural-transformation-Precategory α β =
    map-inv-equiv (extensionality-natural-transformation-Precategory α β)
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
  right-unit-law-comp-natural-transformation-Precategory F G α =
    eq-htpy-hom-family-natural-transformation-Precategory C D F G
      ( comp-natural-transformation-Precategory C D F F G α
        ( id-natural-transformation-Precategory C D F))
      ( α)
      ( right-unit-law-comp-hom-Precategory D ∘
        hom-family-natural-transformation-Precategory C D F G α)

  left-unit-law-comp-natural-transformation-Precategory :
    (F G : functor-Precategory C D)
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F G G
      ( id-natural-transformation-Precategory C D G) α ＝ α
  left-unit-law-comp-natural-transformation-Precategory F G α =
    eq-htpy-hom-family-natural-transformation-Precategory C D F G
      ( comp-natural-transformation-Precategory C D F G G
        ( id-natural-transformation-Precategory C D G) α)
      ( α)
      ( left-unit-law-comp-hom-Precategory D ∘
        hom-family-natural-transformation-Precategory C D F G α)

  associative-comp-natural-transformation-Precategory :
    (F G H I : functor-Precategory C D)
    (α : natural-transformation-Precategory C D F G)
    (β : natural-transformation-Precategory C D G H)
    (γ : natural-transformation-Precategory C D H I) →
    comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I γ β) α ＝
    comp-natural-transformation-Precategory C D F H I γ
      ( comp-natural-transformation-Precategory C D F G H β α)
  associative-comp-natural-transformation-Precategory F G H I α β γ =
    eq-htpy-hom-family-natural-transformation-Precategory C D F I _ _
    ( λ x →
      associative-comp-hom-Precategory D
        ( hom-family-natural-transformation-Precategory C D H I γ x)
        ( hom-family-natural-transformation-Precategory C D G H β x)
        ( hom-family-natural-transformation-Precategory C D F G α x))
```

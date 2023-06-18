# Natural transformations between functors on precategories

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
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given precategories `C` and `D`, a natural transformation from a functor
`F : C → D` to `G : C → D` consists of :

- a family of morphisms `γ : (x : C) → hom (F x) (G x)` such that the following
  identity holds:
- `(G f) ∘ (γ x) = (γ y) ∘ (F f)`, for all `f : hom x y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  is-natural-transformation-Precategory :
    ( (x : obj-Precategory C) →
      type-hom-Precategory D
        ( obj-functor-Precategory C D F x)
        ( obj-functor-Precategory C D G x)) →
    UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-Precategory γ =
    {x y : obj-Precategory C} (f : type-hom-Precategory C x y) →
    ( comp-hom-Precategory D (hom-functor-Precategory C D G f) (γ x)) ＝
    ( comp-hom-Precategory D (γ y) (hom-functor-Precategory C D F f))

  natural-transformation-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-Precategory =
    Σ ( (x : obj-Precategory C) →
        type-hom-Precategory D
          ( obj-functor-Precategory C D F x)
          ( obj-functor-Precategory C D G x))
      is-natural-transformation-Precategory

  components-natural-transformation-Precategory :
    natural-transformation-Precategory → (x : obj-Precategory C) →
    type-hom-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D G x)
  components-natural-transformation-Precategory = pr1

  coherence-square-natural-transformation-Precategory :
    (γ : natural-transformation-Precategory) →
    is-natural-transformation-Precategory
      ( components-natural-transformation-Precategory γ)
  coherence-square-natural-transformation-Precategory = pr2
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  id-natural-transformation-Precategory :
    (F : functor-Precategory C D) → natural-transformation-Precategory C D F F
  pr1 (id-natural-transformation-Precategory F) x = id-hom-Precategory D
  pr2 (id-natural-transformation-Precategory F) f =
    right-unit-law-comp-hom-Precategory D _ ∙
    inv (left-unit-law-comp-hom-Precategory D _)

  comp-natural-transformation-Precategory :
    (F G H : functor-Precategory C D) →
    natural-transformation-Precategory C D G H →
    natural-transformation-Precategory C D F G →
    natural-transformation-Precategory C D F H
  pr1 (comp-natural-transformation-Precategory F G H β α) x =
    comp-hom-Precategory D
      ( components-natural-transformation-Precategory C D G H β x)
      ( components-natural-transformation-Precategory C D F G α x)
  pr2 (comp-natural-transformation-Precategory F G H β α) f =
    equational-reasoning
      comp-hom-Precategory D
        ( hom-functor-Precategory C D H f)
        ( comp-hom-Precategory D
          ( components-natural-transformation-Precategory C D G H β _)
          ( pr1 α _))
      ＝ comp-hom-Precategory D
          ( comp-hom-Precategory D (hom-functor-Precategory C D H f)
            ( components-natural-transformation-Precategory C D G H β _))
          ( pr1 α _)
        by inv (associative-comp-hom-Precategory D _ _ _)
      ＝ comp-hom-Precategory D
          ( comp-hom-Precategory D (pr1 β _) (hom-functor-Precategory C D G f))
          ( components-natural-transformation-Precategory C D F G α _)
        by
          ap
            ( λ x → comp-hom-Precategory D x _)
            ( coherence-square-natural-transformation-Precategory C D G H β f)
      ＝ comp-hom-Precategory D (pr1 β _)
          ( comp-hom-Precategory D
            ( hom-functor-Precategory C D G f)
            ( components-natural-transformation-Precategory C D F G α _))
        by associative-comp-hom-Precategory D _ _ _
      ＝ comp-hom-Precategory D (pr1 β _)
          ( comp-hom-Precategory D
            ( components-natural-transformation-Precategory C D F G α _)
            ( hom-functor-Precategory C D F f))
        by
          ap
            ( comp-hom-Precategory D _)
            ( coherence-square-natural-transformation-Precategory C D F G α f)
      ＝ comp-hom-Precategory D
          ( comp-hom-Precategory D
            ( pr1 β _)
            ( components-natural-transformation-Precategory C D F G α _))
          ( hom-functor-Precategory C D F f)
        by inv (associative-comp-hom-Precategory D _ _ _)
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are sets.

```agda
is-prop-is-natural-transformation-Precategory :
  { l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  ( F G : functor-Precategory C D) →
  ( γ :
    (x : obj-Precategory C) →
    type-hom-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D G x)) →
  is-prop (is-natural-transformation-Precategory C D F G γ)
is-prop-is-natural-transformation-Precategory C D F G γ =
  is-prop-Π'
    ( λ x →
      is-prop-Π'
        ( λ y →
          is-prop-Π
            ( λ f →
              is-set-type-hom-Precategory D
                ( obj-functor-Precategory C D F x)
                ( obj-functor-Precategory C D G y)
                ( comp-hom-Precategory D
                  ( hom-functor-Precategory C D G f)
                  ( γ x))
                ( comp-hom-Precategory D
                  ( γ y)
                  ( hom-functor-Precategory C D F f)))))

is-natural-transformation-Precategory-Prop :
  { l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  ( F G : functor-Precategory C D) →
  ( γ :
    (x : obj-Precategory C) →
    type-hom-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D G x)) →
  Prop (l1 ⊔ l2 ⊔ l4)
is-natural-transformation-Precategory-Prop C D F G α =
  is-natural-transformation-Precategory C D F G α ,
  is-prop-is-natural-transformation-Precategory C D F G α

components-natural-transformation-Precategory-is-emb :
  { l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  ( F G : functor-Precategory C D) →
  is-emb (components-natural-transformation-Precategory C D F G)
components-natural-transformation-Precategory-is-emb C D F G =
  is-emb-inclusion-subtype (is-natural-transformation-Precategory-Prop C D F G)

natural-transformation-Precategory-Set :
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D) →
  Set (l1 ⊔ l2 ⊔ l4)
natural-transformation-Precategory-Set C D F G =
  natural-transformation-Precategory C D F G ,
  is-set-Σ
    ( is-set-Π
      ( λ x →
        is-set-type-hom-Precategory D
          ( obj-functor-Precategory C D F x)
          ( obj-functor-Precategory C D G x)))
    ( λ α →
      pr2 (set-Prop (is-natural-transformation-Precategory-Prop C D F G α)))
```

### Category laws for natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  eq-natural-transformation-Precategory :
    (F G : functor-Precategory C D)
    (α β : natural-transformation-Precategory C D F G) →
    ( components-natural-transformation-Precategory C D F G α ＝
      components-natural-transformation-Precategory C D F G β) →
    α ＝ β
  eq-natural-transformation-Precategory F G α β =
    is-injective-is-emb
      ( components-natural-transformation-Precategory-is-emb C D F G)

  right-unit-law-comp-natural-transformation-Precategory :
    {F G : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F F G α
      ( id-natural-transformation-Precategory C D F) ＝ α
  right-unit-law-comp-natural-transformation-Precategory {F} {G} α =
    eq-natural-transformation-Precategory F G
      ( comp-natural-transformation-Precategory C D F F G α
        ( id-natural-transformation-Precategory C D F))
      ( α)
      ( eq-htpy
        ( right-unit-law-comp-hom-Precategory D ∘
          components-natural-transformation-Precategory C D F G α))

  left-unit-law-comp-natural-transformation-Precategory :
    {F G : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G) →
    comp-natural-transformation-Precategory C D F G G
      ( id-natural-transformation-Precategory C D G) α ＝ α
  left-unit-law-comp-natural-transformation-Precategory {F} {G} α =
    eq-natural-transformation-Precategory F G
      ( comp-natural-transformation-Precategory C D F G G
        ( id-natural-transformation-Precategory C D G) α)
      ( α)
      ( eq-htpy
        ( left-unit-law-comp-hom-Precategory D ∘
          components-natural-transformation-Precategory C D F G α))

  associative-comp-natural-transformation-Precategory :
    {F G H I : functor-Precategory C D}
    (α : natural-transformation-Precategory C D F G)
    (β : natural-transformation-Precategory C D G H)
    (γ : natural-transformation-Precategory C D H I) →
    comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I γ β) α ＝
    comp-natural-transformation-Precategory C D F H I γ
      ( comp-natural-transformation-Precategory C D F G H β α)
  associative-comp-natural-transformation-Precategory {F} {G} {H} {I} α β γ =
    eq-natural-transformation-Precategory F I _ _
    ( eq-htpy λ x →
      associative-comp-hom-Precategory D
        ( components-natural-transformation-Precategory C D H I γ x)
        ( components-natural-transformation-Precategory C D G H β x)
        ( components-natural-transformation-Precategory C D F G α x))
```

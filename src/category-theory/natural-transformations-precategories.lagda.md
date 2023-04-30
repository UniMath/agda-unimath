# Natural transformations between functors on precategories

```agda
module category-theory.natural-transformations-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equational-reasoning
open import foundation.function-extensionality
open import foundation.functions
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
- `compose (G f) (γ x) = compose (γ y) (F f)`, for all `f : hom x y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  (F G : functor-Precat C D)
  where

  is-natural-transformation-Precat :
    ( (x : obj-Precat C) →
      type-hom-Precat D
        ( obj-functor-Precat C D F x)
        ( obj-functor-Precat C D G x)) →
    UU (l1 ⊔ l2 ⊔ l4)
  is-natural-transformation-Precat γ =
    {x y : obj-Precat C} (f : type-hom-Precat C x y) →
    ( comp-hom-Precat D (hom-functor-Precat C D G f) (γ x)) ＝
    ( comp-hom-Precat D (γ y) (hom-functor-Precat C D F f))

  natural-transformation-Precat : UU (l1 ⊔ l2 ⊔ l4)
  natural-transformation-Precat =
    Σ ( (x : obj-Precat C) →
        type-hom-Precat D
          ( obj-functor-Precat C D F x)
          ( obj-functor-Precat C D G x))
      is-natural-transformation-Precat

  components-natural-transformation-Precat :
    natural-transformation-Precat → (x : obj-Precat C) →
    type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G x)
  components-natural-transformation-Precat = pr1

  coherence-square-natural-transformation-Precat :
    (γ : natural-transformation-Precat) →
    is-natural-transformation-Precat
      ( components-natural-transformation-Precat γ)
  coherence-square-natural-transformation-Precat = pr2
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  where

  id-natural-transformation-Precat :
    (F : functor-Precat C D) → natural-transformation-Precat C D F F
  pr1 (id-natural-transformation-Precat F) x = id-hom-Precat D
  pr2 (id-natural-transformation-Precat F) f =
    right-unit-law-comp-hom-Precat D _ ∙
    inv (left-unit-law-comp-hom-Precat D _)

  comp-natural-transformation-Precat :
     (F G H : functor-Precat C D) →
     natural-transformation-Precat C D G H →
     natural-transformation-Precat C D F G →
     natural-transformation-Precat C D F H
  pr1 (comp-natural-transformation-Precat F G H β α) x =
    comp-hom-Precat D
      ( components-natural-transformation-Precat C D G H β x)
      ( components-natural-transformation-Precat C D F G α x)
  pr2 (comp-natural-transformation-Precat F G H β α) f =
    equational-reasoning
      comp-hom-Precat D
        ( hom-functor-Precat C D H f)
        ( comp-hom-Precat D
          ( components-natural-transformation-Precat C D G H β _)
          ( pr1 α _))
      ＝ comp-hom-Precat D
          ( comp-hom-Precat D (hom-functor-Precat C D H f)
            ( components-natural-transformation-Precat C D G H β _))
          ( pr1 α _)
        by inv (associative-comp-hom-Precat D _ _ _)
      ＝ comp-hom-Precat D
          ( comp-hom-Precat D (pr1 β _) (hom-functor-Precat C D G f))
          ( components-natural-transformation-Precat C D F G α _)
        by
          ap
            ( λ x → comp-hom-Precat D x _)
            ( coherence-square-natural-transformation-Precat C D G H β f)
      ＝ comp-hom-Precat D (pr1 β _)
          ( comp-hom-Precat D
            ( hom-functor-Precat C D G f)
            ( components-natural-transformation-Precat C D F G α _))
        by associative-comp-hom-Precat D _ _ _
      ＝ comp-hom-Precat D (pr1 β _)
          ( comp-hom-Precat D
            ( components-natural-transformation-Precat C D F G α _)
            ( hom-functor-Precat C D F f))
        by
          ap
            ( comp-hom-Precat D _)
            ( coherence-square-natural-transformation-Precat C D F G α f)
      ＝ comp-hom-Precat D
          ( comp-hom-Precat D
            ( pr1 β _)
            ( components-natural-transformation-Precat C D F G α _))
          ( hom-functor-Precat C D F f)
        by inv (associative-comp-hom-Precat D _ _ _)
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are sets.

```agda
is-prop-is-natural-transformation-Precat :
  { l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  ( F G : functor-Precat C D) →
  ( γ :
    (x : obj-Precat C) →
    type-hom-Precat D
      ( obj-functor-Precat C D F x)
      ( obj-functor-Precat C D G x)) →
  is-prop (is-natural-transformation-Precat C D F G γ)
is-prop-is-natural-transformation-Precat C D F G γ =
  is-prop-Π'
    ( λ x →
      is-prop-Π'
        ( λ y →
          is-prop-Π
            ( λ f →
              is-set-type-hom-Precat D
                ( obj-functor-Precat C D F x)
                ( obj-functor-Precat C D G y)
                ( comp-hom-Precat D (hom-functor-Precat C D G f) (γ x))
                ( comp-hom-Precat D (γ y) (hom-functor-Precat C D F f)))))

is-natural-transformation-Precat-Prop :
  { l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  ( F G : functor-Precat C D) →
  ( γ :
    (x : obj-Precat C) →
    type-hom-Precat D
      ( obj-functor-Precat C D F x)
      ( obj-functor-Precat C D G x)) →
  Prop (l1 ⊔ l2 ⊔ l4)
is-natural-transformation-Precat-Prop C D F G α =
  is-natural-transformation-Precat C D F G α ,
  is-prop-is-natural-transformation-Precat C D F G α

components-natural-transformation-Precat-is-emb :
  { l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  ( F G : functor-Precat C D) →
  is-emb (components-natural-transformation-Precat C D F G)
components-natural-transformation-Precat-is-emb C D F G =
  is-emb-inclusion-subtype (is-natural-transformation-Precat-Prop C D F G)

natural-transformation-Precat-Set :
  {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  (F G : functor-Precat C D) →
  Set (l1 ⊔ l2 ⊔ l4)
natural-transformation-Precat-Set C D F G =
  natural-transformation-Precat C D F G ,
  is-set-Σ
    ( is-set-Π
      ( λ x →
        is-set-type-hom-Precat D
          ( obj-functor-Precat C D F x)
          ( obj-functor-Precat C D G x)))
    ( λ α → pr2 (set-Prop (is-natural-transformation-Precat-Prop C D F G α)))
```

### Category laws for natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  where

  eq-natural-transformation-Precat :
    (F G : functor-Precat C D)
    (α β : natural-transformation-Precat C D F G) →
    ( components-natural-transformation-Precat C D F G α ＝
      components-natural-transformation-Precat C D F G β) →
    α ＝ β
  eq-natural-transformation-Precat F G α β =
    is-injective-is-emb
      ( components-natural-transformation-Precat-is-emb C D F G)

  right-unit-law-comp-natural-transformation-Precat :
    {F G : functor-Precat C D} (α : natural-transformation-Precat C D F G) →
    comp-natural-transformation-Precat C D F F G α
      ( id-natural-transformation-Precat C D F) ＝ α
  right-unit-law-comp-natural-transformation-Precat {F} {G} α =
    eq-natural-transformation-Precat F G
      ( comp-natural-transformation-Precat C D F F G α
        ( id-natural-transformation-Precat C D F))
      ( α)
      ( eq-htpy
        ( right-unit-law-comp-hom-Precat D ∘
          components-natural-transformation-Precat C D F G α))

  left-unit-law-comp-natural-transformation-Precat :
    {F G : functor-Precat C D}
    (α : natural-transformation-Precat C D F G) →
    comp-natural-transformation-Precat C D F G G
      ( id-natural-transformation-Precat C D G) α ＝ α
  left-unit-law-comp-natural-transformation-Precat {F} {G} α =
    eq-natural-transformation-Precat F G
      ( comp-natural-transformation-Precat C D F G G
        ( id-natural-transformation-Precat C D G) α)
      ( α)
      ( eq-htpy
        ( left-unit-law-comp-hom-Precat D ∘
          components-natural-transformation-Precat C D F G α))

  associative-comp-natural-transformation-Precat :
    {F G H I : functor-Precat C D}
    (α : natural-transformation-Precat C D F G)
    (β : natural-transformation-Precat C D G H)
    (γ : natural-transformation-Precat C D H I) →
    comp-natural-transformation-Precat C D F G I
      ( comp-natural-transformation-Precat C D G H I γ β) α ＝
    comp-natural-transformation-Precat C D F H I γ
      ( comp-natural-transformation-Precat C D F G H β α)
  associative-comp-natural-transformation-Precat {F} {G} {H} {I} α β γ =
    eq-natural-transformation-Precat F I _ _
    ( eq-htpy λ x →
      associative-comp-hom-Precat D
        ( components-natural-transformation-Precat C D H I γ x)
        ( components-natural-transformation-Precat C D G H β x)
        ( components-natural-transformation-Precat C D F G α x))
```

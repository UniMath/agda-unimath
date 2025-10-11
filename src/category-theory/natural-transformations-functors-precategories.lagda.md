# Natural transformations between functors between precategories

```agda
module category-theory.natural-transformations-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
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

  naturality-natural-transformation-Precategory :
    (γ : natural-transformation-Precategory) →
    is-natural-transformation-Precategory
      ( hom-family-natural-transformation-Precategory γ)
  naturality-natural-transformation-Precategory =
    naturality-natural-transformation-map-Precategory C D
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

## Equality of functors induces a natural transformation

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  natural-transformation-eq-Precategory :
    (F G : functor-Precategory C D) →
    F ＝ G →
    natural-transformation-Precategory C D F G
  natural-transformation-eq-Precategory F G refl =
    id-natural-transformation-Precategory C D F

  natural-transformation-eq-inv-Precategory :
    (F G : functor-Precategory C D) →
    F ＝ G →
    natural-transformation-Precategory C D G F
  natural-transformation-eq-inv-Precategory F G =
    natural-transformation-eq-Precategory G F ∘ inv
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

  htpy-eq-hom-family-natural-transformation-Precategory :
    {α β : natural-transformation-Precategory C D F G} →
    α ＝ β →
    hom-family-natural-transformation-Precategory C D F G α ~
    hom-family-natural-transformation-Precategory C D F G β
  htpy-eq-hom-family-natural-transformation-Precategory =
    htpy-eq-hom-family-natural-transformation-map-Precategory C D
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

  involutive-eq-associative-comp-natural-transformation-Precategory :
    (F G H I : functor-Precategory C D)
    (α : natural-transformation-Precategory C D F G)
    (β : natural-transformation-Precategory C D G H)
    (γ : natural-transformation-Precategory C D H I) →
    comp-natural-transformation-Precategory C D F G I
      ( comp-natural-transformation-Precategory C D G H I γ β) α ＝ⁱ
    comp-natural-transformation-Precategory C D F H I γ
      ( comp-natural-transformation-Precategory C D F G H β α)
  involutive-eq-associative-comp-natural-transformation-Precategory F G H I =
    involutive-eq-associative-comp-natural-transformation-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)
      ( map-functor-Precategory C D H)
      ( map-functor-Precategory C D I)
```

## Whiskering

If `α : F ⇒ G` is a natural transformations between functors `F, G : C → D`, and
`H : D → E` is another functor, we can form the natural transformation
`H • α : H ∘ F ⇒ H ∘ G`. Its component at `x` is `(H • α)(x) = H(α(x))`.

On the other hand, if we have a functor `K : B → C`, we can form a natural
transformation `α • K : F ∘ K ⇒ G ∘ K`. Its component at `x` is
`(α • K)(x) = α(K(x))`.

Here, `•` denotes _whiskering_. Note that there are two kinds of whiskering,
depending on whether the first or the second parameter expects a natural
transformation.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (E : Precategory l5 l6)
  where

  left-whisker-natural-transformation-Precategory :
    (F G : functor-Precategory C D)
    (H : functor-Precategory D E)
    (α : natural-transformation-Precategory C D F G) →
    natural-transformation-Precategory
      ( C)
      ( E)
      ( comp-functor-Precategory C D E H F)
      ( comp-functor-Precategory C D E H G)
  left-whisker-natural-transformation-Precategory F G H α =
    ( λ x →
      hom-functor-Precategory D E H (hom-family-natural-transformation-Precategory C D F G α x)) ,
    ( λ {x} {y} f →
      inv
        ( preserves-comp-functor-Precategory
          ( D)
          ( E)
          ( H)
          ( hom-functor-Precategory C D G f)
          ( hom-family-natural-transformation-Precategory C D F G α x)) ∙
      ( ap
        ( hom-functor-Precategory D E H)
        ( naturality-natural-transformation-Precategory C D F G α f)) ∙
      ( preserves-comp-functor-Precategory
        ( D)
        ( E)
        ( H)
        ( hom-family-natural-transformation-Precategory C D F G α y)
        ( hom-functor-Precategory C D F f)))

  preserves-comp-left-whisker-natural-transformation-Precategory :
    (F G H : functor-Precategory C D)
    (I : functor-Precategory D E)
    (β : natural-transformation-Precategory C D G H)
    (α : natural-transformation-Precategory C D F G) →
    left-whisker-natural-transformation-Precategory
      ( F)
      ( H)
      ( I)
      ( comp-natural-transformation-Precategory C D F G H β α) ＝
    comp-natural-transformation-Precategory
      ( C)
      ( E)
      ( comp-functor-Precategory C D E I F)
      ( comp-functor-Precategory C D E I G)
      ( comp-functor-Precategory C D E I H)
      ( left-whisker-natural-transformation-Precategory G H I β)
      ( left-whisker-natural-transformation-Precategory F G I α)
  preserves-comp-left-whisker-natural-transformation-Precategory F G H I β α =
    eq-htpy-hom-family-natural-transformation-Precategory C E
      ( comp-functor-Precategory C D E I F)
      ( comp-functor-Precategory C D E I H)
      ( _)
      ( _)
      ( λ x → preserves-comp-functor-Precategory D E I _ _)

  preserves-id-left-whisker-natural-transformation-Precategory :
    (F : functor-Precategory C D)
    (H : functor-Precategory D E) →
    left-whisker-natural-transformation-Precategory F F
      ( H)
      ( id-natural-transformation-Precategory C D F) ＝
    id-natural-transformation-Precategory C E
      ( comp-functor-Precategory C D E H F)
  preserves-id-left-whisker-natural-transformation-Precategory F H =
    eq-htpy-hom-family-natural-transformation-Precategory C E
      ( comp-functor-Precategory C D E H F)
      ( comp-functor-Precategory C D E H F)
      ( _)
      ( _)
      ( λ x → preserves-id-functor-Precategory D E H _)

  right-whisker-natural-transformation-Precategory :
    (F G : functor-Precategory C D)
    (α : natural-transformation-Precategory C D F G)
    (K : functor-Precategory E C) →
    natural-transformation-Precategory
      ( E)
      ( D)
      ( comp-functor-Precategory E C D F K)
      ( comp-functor-Precategory E C D G K)
  right-whisker-natural-transformation-Precategory F G α K =
    ( λ x →
      hom-family-natural-transformation-Precategory C D F G
        ( α)
        ( obj-functor-Precategory E C K x)) ,
    ( λ f →
      naturality-natural-transformation-Precategory C D F G
        ( α)
        ( hom-functor-Precategory E C K f))

  preserves-comp-right-whisker-natural-transformation-Precategory :
    (F G H : functor-Precategory C D)
    (β : natural-transformation-Precategory C D G H)
    (α : natural-transformation-Precategory C D F G)
    (I : functor-Precategory E C) →
    right-whisker-natural-transformation-Precategory
      ( F)
      ( H)
      ( comp-natural-transformation-Precategory C D F G H β α)
      ( I) ＝
    comp-natural-transformation-Precategory
      ( E)
      ( D)
      ( comp-functor-Precategory E C D F I)
      ( comp-functor-Precategory E C D G I)
      ( comp-functor-Precategory E C D H I)
      ( right-whisker-natural-transformation-Precategory G H β I)
      ( right-whisker-natural-transformation-Precategory F G α I)
  preserves-comp-right-whisker-natural-transformation-Precategory F G H β α I =
    refl
```

## Horizontal composition

Horizontal composition (here denoted by `*`) is generalized
[whiskering](category-theory.natural-transformations-functors-precategories.md#whiskering)
(here denoted by `•`), and also defined by it. Given natural transformations
`α : F ⇒ G`, `F, G : C → D`, and `β : H ⇒ I`, `H, I : D → E`, we can form a
natural transformation `β * α : H ∘ F ⇒ I ∘ G`.

More precisely, `β * α = (β • G) ∘ (H • α)`, that is, we compose two natural
transformations obtained by whiskering.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (E : Precategory l5 l6)
  where

  horizontal-comp-natural-transformation-Precategory :
    (F G : functor-Precategory C D)
    (H I : functor-Precategory D E)
    (β : natural-transformation-Precategory D E H I)
    (α : natural-transformation-Precategory C D F G) →
    natural-transformation-Precategory
      ( C)
      ( E)
      ( comp-functor-Precategory C D E H F)
      ( comp-functor-Precategory C D E I G)
  horizontal-comp-natural-transformation-Precategory F G H I β α =
    comp-natural-transformation-Precategory C E
      ( comp-functor-Precategory C D E H F)
      ( comp-functor-Precategory C D E H G)
      ( comp-functor-Precategory C D E I G)
      ( right-whisker-natural-transformation-Precategory D E C H I β G)
      ( left-whisker-natural-transformation-Precategory C D E F G H α)
```

# Natural transformations between maps from small to large precategories

```agda
module category-theory.natural-transformations-maps-from-small-to-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategories
open import category-theory.large-precategories
open import category-theory.maps-from-small-to-large-precategories
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

Given a small [precategory](category-theory.precategories.md) `C` and a
[large precategory](category-theory.large-precategories.md) `D`, a **natural
transformation** from a
[map of precategories](category-theory.maps-from-small-to-large-precategories.md)
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
  (F : map-Small-Large-Precategory C D γF)
  (G : map-Small-Large-Precategory C D γG)
  where

  hom-family-map-Small-Large-Precategory : UU (l1 ⊔ β γF γG)
  hom-family-map-Small-Large-Precategory =
    (x : obj-Precategory C) →
    hom-Large-Precategory D
      ( obj-map-Small-Large-Precategory C D F x)
      ( obj-map-Small-Large-Precategory C D G x)

  naturality-hom-family-map-Small-Large-Precategory :
    hom-family-map-Small-Large-Precategory →
    {x y : obj-Precategory C} (f : hom-Precategory C x y) → UU (β γF γG)
  naturality-hom-family-map-Small-Large-Precategory γ {x} {y} f =
    coherence-square-hom-Large-Precategory D
      ( hom-map-Small-Large-Precategory C D F f)
      ( γ x)
      ( γ y)
      ( hom-map-Small-Large-Precategory C D G f)

  is-natural-transformation-map-Small-Large-Precategory :
    hom-family-map-Small-Large-Precategory → UU (l1 ⊔ l2 ⊔ β γF γG)
  is-natural-transformation-map-Small-Large-Precategory γ =
    {x y : obj-Precategory C} (f : hom-Precategory C x y) →
    naturality-hom-family-map-Small-Large-Precategory γ f

  natural-transformation-map-Small-Large-Precategory : UU (l1 ⊔ l2 ⊔ β γF γG)
  natural-transformation-map-Small-Large-Precategory =
    Σ ( hom-family-map-Small-Large-Precategory)
      ( is-natural-transformation-map-Small-Large-Precategory)

  hom-natural-transformation-map-Small-Large-Precategory :
    natural-transformation-map-Small-Large-Precategory →
    hom-family-map-Small-Large-Precategory
  hom-natural-transformation-map-Small-Large-Precategory = pr1

  naturality-natural-transformation-map-Small-Large-Precategory :
    (γ : natural-transformation-map-Small-Large-Precategory) →
    is-natural-transformation-map-Small-Large-Precategory
      ( hom-natural-transformation-map-Small-Large-Precategory γ)
  naturality-natural-transformation-map-Small-Large-Precategory = pr2
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  id-natural-transformation-map-Small-Large-Precategory :
    {γF : Level} (F : map-Small-Large-Precategory C D γF) →
    natural-transformation-map-Small-Large-Precategory C D F F
  pr1 (id-natural-transformation-map-Small-Large-Precategory F) x =
    id-hom-Large-Precategory D
  pr2 (id-natural-transformation-map-Small-Large-Precategory F) f =
    ( right-unit-law-comp-hom-Large-Precategory D
      ( hom-map-Small-Large-Precategory C D F f)) ∙
    ( inv
      ( left-unit-law-comp-hom-Large-Precategory D
        ( hom-map-Small-Large-Precategory C D F f)))

  comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG γH : Level}
    (F : map-Small-Large-Precategory C D γF) →
    (G : map-Small-Large-Precategory C D γG) →
    (H : map-Small-Large-Precategory C D γH) →
    natural-transformation-map-Small-Large-Precategory C D G H →
    natural-transformation-map-Small-Large-Precategory C D F G →
    natural-transformation-map-Small-Large-Precategory C D F H
  pr1 (comp-natural-transformation-map-Small-Large-Precategory F G H β α) x =
    comp-hom-Large-Precategory D
      ( hom-natural-transformation-map-Small-Large-Precategory
          C D G H β x)
      ( hom-natural-transformation-map-Small-Large-Precategory
          C D F G α x)
  pr2
    ( comp-natural-transformation-map-Small-Large-Precategory F G H β α)
    { X} {Y} f =
    ( inv
      ( associative-comp-hom-Large-Precategory D
        ( hom-map-Small-Large-Precategory C D H f)
        ( hom-natural-transformation-map-Small-Large-Precategory
            C D G H β X)
        ( hom-natural-transformation-map-Small-Large-Precategory
            C D F G α X))) ∙
    ( ap
      ( comp-hom-Large-Precategory' D
        ( hom-natural-transformation-map-Small-Large-Precategory
            C D F G α X))
      ( naturality-natural-transformation-map-Small-Large-Precategory
          C D G H β f)) ∙
    ( associative-comp-hom-Large-Precategory D
      ( hom-natural-transformation-map-Small-Large-Precategory
          C D G H β Y)
      ( hom-map-Small-Large-Precategory C D G f)
      ( hom-natural-transformation-map-Small-Large-Precategory
          C D F G α X)) ∙
    ( ap
      ( comp-hom-Large-Precategory D
        ( hom-natural-transformation-map-Small-Large-Precategory
            C D G H β Y))
      ( naturality-natural-transformation-map-Small-Large-Precategory
          C D F G α f)) ∙
    ( inv
      ( associative-comp-hom-Large-Precategory D
        ( hom-natural-transformation-map-Small-Large-Precategory
            C D G H β Y)
        ( hom-natural-transformation-map-Small-Large-Precategory
            C D F G α Y)
        ( hom-map-Small-Large-Precategory C D F f)))
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
  (F : map-Small-Large-Precategory C D γF)
  (G : map-Small-Large-Precategory C D γG)
  where

  is-prop-is-natural-transformation-map-Small-Large-Precategory :
    (a : hom-family-map-Small-Large-Precategory C D F G) →
    is-prop (is-natural-transformation-map-Small-Large-Precategory C D F G a)
  is-prop-is-natural-transformation-map-Small-Large-Precategory a =
    is-prop-implicit-Π
      ( λ x →
        is-prop-implicit-Π
          ( λ y →
            is-prop-Π
              ( λ f →
                is-set-hom-Large-Precategory D
                  ( obj-map-Small-Large-Precategory C D F x)
                  ( obj-map-Small-Large-Precategory C D G y)
                  ( comp-hom-Large-Precategory D
                    ( hom-map-Small-Large-Precategory C D G f)
                    ( a x))
                  ( comp-hom-Large-Precategory D
                    ( a y)
                    ( hom-map-Small-Large-Precategory C D F f)))))

  is-natural-transformation-prop-map-Small-Large-Precategory :
    (a : hom-family-map-Small-Large-Precategory C D F G) →
    Prop (l1 ⊔ l2 ⊔ β γF γG)
  pr1 (is-natural-transformation-prop-map-Small-Large-Precategory a) =
    is-natural-transformation-map-Small-Large-Precategory C D F G a
  pr2 (is-natural-transformation-prop-map-Small-Large-Precategory a) =
    is-prop-is-natural-transformation-map-Small-Large-Precategory a
```

### The set of natural transformations

```agda
module _
  {l1 l2 γF γG : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (F : map-Small-Large-Precategory C D γF)
  (G : map-Small-Large-Precategory C D γG)
  where

  is-emb-hom-natural-transformation-map-Small-Large-Precategory :
    is-emb
      ( hom-natural-transformation-map-Small-Large-Precategory C D F G)
  is-emb-hom-natural-transformation-map-Small-Large-Precategory =
    is-emb-inclusion-subtype
      ( is-natural-transformation-prop-map-Small-Large-Precategory C D F G)

  emb-hom-natural-transformation-map-Small-Large-Precategory :
    natural-transformation-map-Small-Large-Precategory C D F G ↪
    hom-family-map-Small-Large-Precategory C D F G
  emb-hom-natural-transformation-map-Small-Large-Precategory =
    emb-subtype
      ( is-natural-transformation-prop-map-Small-Large-Precategory C D F G)

  is-set-natural-transformation-map-Small-Large-Precategory :
    is-set (natural-transformation-map-Small-Large-Precategory C D F G)
  is-set-natural-transformation-map-Small-Large-Precategory =
    is-set-Σ
      ( is-set-Π
        ( λ x →
          is-set-hom-Large-Precategory D
            ( obj-map-Small-Large-Precategory C D F x)
            ( obj-map-Small-Large-Precategory C D G x)))
      ( λ α →
        is-set-type-Set
          ( set-Prop
            ( is-natural-transformation-prop-map-Small-Large-Precategory
                C D F G α)))

  natural-transformation-map-set-Small-Large-Precategory :
    Set (l1 ⊔ l2 ⊔ β γF γG)
  pr1 (natural-transformation-map-set-Small-Large-Precategory) =
    natural-transformation-map-Small-Large-Precategory C D F G
  pr2 (natural-transformation-map-set-Small-Large-Precategory) =
    is-set-natural-transformation-map-Small-Large-Precategory

  extensionality-natural-transformation-map-Small-Large-Precategory :
    (α β : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( α ＝ β) ≃
    ( hom-natural-transformation-map-Small-Large-Precategory C D F G α ~
      hom-natural-transformation-map-Small-Large-Precategory C D F G β)
  extensionality-natural-transformation-map-Small-Large-Precategory α β =
    ( equiv-funext) ∘e
    ( equiv-ap-emb
        emb-hom-natural-transformation-map-Small-Large-Precategory)

  eq-htpy-hom-natural-transformation-map-Small-Large-Precategory :
    (α β : natural-transformation-map-Small-Large-Precategory C D F G) →
    ( hom-natural-transformation-map-Small-Large-Precategory C D F G α ~
      hom-natural-transformation-map-Small-Large-Precategory C D F G β) →
    α ＝ β
  eq-htpy-hom-natural-transformation-map-Small-Large-Precategory α β =
    map-inv-equiv
      ( extensionality-natural-transformation-map-Small-Large-Precategory α β)
```

### Categorical laws for natural transformations

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  where

  right-unit-law-comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG : Level}
    (F : map-Small-Large-Precategory C D γF)
    (G : map-Small-Large-Precategory C D γG)
    (a : natural-transformation-map-Small-Large-Precategory C D F G) →
    comp-natural-transformation-map-Small-Large-Precategory C D F F G a
      ( id-natural-transformation-map-Small-Large-Precategory C D F) ＝ a
  right-unit-law-comp-natural-transformation-map-Small-Large-Precategory F G a =
    eq-htpy-hom-natural-transformation-map-Small-Large-Precategory
      C D F G
      ( comp-natural-transformation-map-Small-Large-Precategory C D F F G a
        ( id-natural-transformation-map-Small-Large-Precategory C D F))
      ( a)
      ( right-unit-law-comp-hom-Large-Precategory D ∘
        hom-natural-transformation-map-Small-Large-Precategory C D F G a)

  left-unit-law-comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG : Level}
    (F : map-Small-Large-Precategory C D γF)
    (G : map-Small-Large-Precategory C D γG)
    (a : natural-transformation-map-Small-Large-Precategory C D F G) →
    comp-natural-transformation-map-Small-Large-Precategory C D F G G
      ( id-natural-transformation-map-Small-Large-Precategory C D G) a ＝ a
  left-unit-law-comp-natural-transformation-map-Small-Large-Precategory F G a =
    eq-htpy-hom-natural-transformation-map-Small-Large-Precategory
      C D F G
      ( comp-natural-transformation-map-Small-Large-Precategory C D F G G
        ( id-natural-transformation-map-Small-Large-Precategory C D G) a)
      ( a)
      ( left-unit-law-comp-hom-Large-Precategory D ∘
        hom-natural-transformation-map-Small-Large-Precategory C D F G a)

  associative-comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG γH γI : Level}
    (F : map-Small-Large-Precategory C D γF)
    (G : map-Small-Large-Precategory C D γG)
    (H : map-Small-Large-Precategory C D γH)
    (I : map-Small-Large-Precategory C D γI)
    (a : natural-transformation-map-Small-Large-Precategory C D F G)
    (b : natural-transformation-map-Small-Large-Precategory C D G H)
    (c : natural-transformation-map-Small-Large-Precategory C D H I) →
    comp-natural-transformation-map-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-map-Small-Large-Precategory C D G H I c b)
      ( a) ＝
    comp-natural-transformation-map-Small-Large-Precategory C D F H I c
      ( comp-natural-transformation-map-Small-Large-Precategory C D F G H b a)
  associative-comp-natural-transformation-map-Small-Large-Precategory
    F G H I a b c =
    eq-htpy-hom-natural-transformation-map-Small-Large-Precategory
      C D F I _ _
      ( λ x →
        associative-comp-hom-Large-Precategory D
          ( hom-natural-transformation-map-Small-Large-Precategory
            C D H I c x)
          ( hom-natural-transformation-map-Small-Large-Precategory
            C D G H b x)
          ( hom-natural-transformation-map-Small-Large-Precategory
            C D F G a x))

  involutive-eq-associative-comp-natural-transformation-map-Small-Large-Precategory :
    {γF γG γH γI : Level}
    (F : map-Small-Large-Precategory C D γF)
    (G : map-Small-Large-Precategory C D γG)
    (H : map-Small-Large-Precategory C D γH)
    (I : map-Small-Large-Precategory C D γI)
    (a : natural-transformation-map-Small-Large-Precategory C D F G)
    (b : natural-transformation-map-Small-Large-Precategory C D G H)
    (c : natural-transformation-map-Small-Large-Precategory C D H I) →
    comp-natural-transformation-map-Small-Large-Precategory C D F G I
      ( comp-natural-transformation-map-Small-Large-Precategory C D G H I c b)
      ( a) ＝ⁱ
    comp-natural-transformation-map-Small-Large-Precategory C D F H I c
      ( comp-natural-transformation-map-Small-Large-Precategory C D F G H b a)
  involutive-eq-associative-comp-natural-transformation-map-Small-Large-Precategory
    F G H I a b c =
    involutive-eq-eq
      ( associative-comp-natural-transformation-map-Small-Large-Precategory
          F G H I a b c)
```

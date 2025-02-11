# Functors from small to large categories

```agda
module category-theory.functors-from-small-to-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.functors-from-small-to-large-precategories
open import category-theory.large-categories
open import category-theory.maps-from-small-to-large-categories

open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [(small) category](category-theory.categories.md) `C` to a
[large category](category-theory.large-categories.md) `D` consists of:

- a map `C → D` on objects at some chosen universe level `γ`,
- a map `hom x y → hom (F x) (F y)` on morphisms, such that the following
  identities hold:
- `F id_x = id_(F x)`,
- `F (g ∘ f) = F g ∘ F f`.

## Definition

### The predicate on maps from small to large categories of being a functor

```agda
module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2) (D : Large-Category α β)
  (F : map-Small-Large-Category C D γ)
  where

  preserves-comp-hom-map-Small-Large-Category : UU (l1 ⊔ l2 ⊔ β γ γ)
  preserves-comp-hom-map-Small-Large-Category =
    preserves-comp-hom-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  preserves-id-hom-map-Small-Large-Category : UU (l1 ⊔ β γ γ)
  preserves-id-hom-map-Small-Large-Category =
    preserves-id-hom-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  is-functor-map-Small-Large-Category : UU (l1 ⊔ l2 ⊔ β γ γ)
  is-functor-map-Small-Large-Category =
    is-functor-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  preserves-comp-is-functor-map-Small-Large-Category :
    is-functor-map-Small-Large-Category →
    preserves-comp-hom-map-Small-Large-Category
  preserves-comp-is-functor-map-Small-Large-Category =
    preserves-comp-is-functor-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  preserves-id-is-functor-map-Small-Large-Category :
    is-functor-map-Small-Large-Category →
    preserves-id-hom-map-Small-Large-Category
  preserves-id-is-functor-map-Small-Large-Category =
    preserves-id-is-functor-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)
```

### Functors from small to large categories

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2) (D : Large-Category α β)
  where

  functor-Small-Large-Category :
    (γ : Level) → UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  functor-Small-Large-Category =
    functor-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)

module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2) (D : Large-Category α β)
  {γ : Level} (F : functor-Small-Large-Category C D γ)
  where

  obj-functor-Small-Large-Category :
    obj-Category C → obj-Large-Category D γ
  obj-functor-Small-Large-Category =
    obj-functor-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  hom-functor-Small-Large-Category :
    {x y : obj-Category C} →
    (f : hom-Category C x y) →
    hom-Large-Category D
      ( obj-functor-Small-Large-Category x)
      ( obj-functor-Small-Large-Category y)
  hom-functor-Small-Large-Category =
    hom-functor-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  map-functor-Small-Large-Category :
    map-Small-Large-Category C D γ
  map-functor-Small-Large-Category =
    map-functor-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  is-functor-functor-Small-Large-Category :
    is-functor-map-Small-Large-Category C D
      ( map-functor-Small-Large-Category)
  is-functor-functor-Small-Large-Category =
    is-functor-functor-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)

  preserves-comp-functor-Small-Large-Category :
    {x y z : obj-Category C}
    (g : hom-Category C y z) (f : hom-Category C x y) →
    ( hom-functor-Small-Large-Category (comp-hom-Category C g f)) ＝
    ( comp-hom-Large-Category D
      ( hom-functor-Small-Large-Category g)
      ( hom-functor-Small-Large-Category f))
  preserves-comp-functor-Small-Large-Category =
    preserves-comp-is-functor-map-Small-Large-Category C D
      ( map-functor-Small-Large-Category)
      ( is-functor-functor-Small-Large-Category)

  preserves-id-functor-Small-Large-Category :
    (x : obj-Category C) →
    ( hom-functor-Small-Large-Category (id-hom-Category C {x})) ＝
    ( id-hom-Large-Category D {γ} {obj-functor-Small-Large-Category x})
  preserves-id-functor-Small-Large-Category =
    preserves-id-is-functor-map-Small-Large-Category C D
      ( map-functor-Small-Large-Category)
      ( is-functor-functor-Small-Large-Category)
```

## Properties

### Characterizing equality of functors from small to large categories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2) (D : Large-Category α β)
  (F G : functor-Small-Large-Category C D γ)
  where

  equiv-eq-map-eq-functor-Small-Large-Category :
    ( F ＝ G) ≃
    ( map-functor-Small-Large-Category C D F ＝
      map-functor-Small-Large-Category C D G)
  equiv-eq-map-eq-functor-Small-Large-Category =
    equiv-eq-map-eq-functor-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  eq-map-eq-functor-Small-Large-Category :
    (F ＝ G) →
    ( map-functor-Small-Large-Category C D F ＝
      map-functor-Small-Large-Category C D G)
  eq-map-eq-functor-Small-Large-Category =
    map-equiv equiv-eq-map-eq-functor-Small-Large-Category

  eq-eq-map-functor-Small-Large-Category :
    ( map-functor-Small-Large-Category C D F ＝
      map-functor-Small-Large-Category C D G) →
    ( F ＝ G)
  eq-eq-map-functor-Small-Large-Category =
    map-inv-equiv equiv-eq-map-eq-functor-Small-Large-Category

  is-section-eq-eq-map-functor-Small-Large-Category :
    ( eq-map-eq-functor-Small-Large-Category ∘
      eq-eq-map-functor-Small-Large-Category) ~
    id
  is-section-eq-eq-map-functor-Small-Large-Category =
    is-section-map-inv-equiv equiv-eq-map-eq-functor-Small-Large-Category

  is-retraction-eq-eq-map-functor-Small-Large-Category :
    ( eq-eq-map-functor-Small-Large-Category ∘
      eq-map-eq-functor-Small-Large-Category) ~
    id
  is-retraction-eq-eq-map-functor-Small-Large-Category =
    is-retraction-map-inv-equiv equiv-eq-map-eq-functor-Small-Large-Category
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2) (D : Large-Category α β)
  (F G : functor-Small-Large-Category C D γ)
  where

  htpy-functor-Small-Large-Category : UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  htpy-functor-Small-Large-Category =
    htpy-functor-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  equiv-htpy-eq-functor-Small-Large-Category :
    (F ＝ G) ≃ htpy-functor-Small-Large-Category
  equiv-htpy-eq-functor-Small-Large-Category =
    equiv-htpy-eq-functor-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( F)
      ( G)

  htpy-eq-functor-Small-Large-Category :
    (F ＝ G) → htpy-functor-Small-Large-Category
  htpy-eq-functor-Small-Large-Category =
    map-equiv equiv-htpy-eq-functor-Small-Large-Category

  eq-htpy-functor-Small-Large-Category :
    htpy-functor-Small-Large-Category → F ＝ G
  eq-htpy-functor-Small-Large-Category =
    map-inv-equiv equiv-htpy-eq-functor-Small-Large-Category

  is-section-eq-htpy-functor-Small-Large-Category :
    ( htpy-eq-functor-Small-Large-Category ∘
      eq-htpy-functor-Small-Large-Category) ~
    id
  is-section-eq-htpy-functor-Small-Large-Category =
    is-section-map-inv-equiv equiv-htpy-eq-functor-Small-Large-Category

  is-retraction-eq-htpy-functor-Small-Large-Category :
    ( eq-htpy-functor-Small-Large-Category ∘
      htpy-eq-functor-Small-Large-Category) ~
    id
  is-retraction-eq-htpy-functor-Small-Large-Category =
    is-retraction-map-inv-equiv
      equiv-htpy-eq-functor-Small-Large-Category
```

## See also

- [The category of functors and natural transformations from small to large categories](category-theory.category-of-functors-from-small-to-large-categories.md)

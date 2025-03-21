# Functors from small to large precategories

```agda
module category-theory.functors-from-small-to-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.large-precategories
open import category-theory.maps-from-small-to-large-precategories
open import category-theory.precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [(small) precategory](category-theory.precategories.md) `C`
to a [large precategory](category-theory.large-precategories.md) `D` consists
of:

- a map `F₀ : C → D` on objects at some chosen universe level `γ`,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identities hold:
- `F id_x = id_(F x)`,
- `F (g ∘ f) = F g ∘ F f`.

## Definition

### The predicate on maps from small to large precategories of being a functor

```agda
module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  (F : map-Small-Large-Precategory C D γ)
  where

  preserves-comp-hom-map-Small-Large-Precategory : UU (l1 ⊔ l2 ⊔ β γ γ)
  preserves-comp-hom-map-Small-Large-Precategory =
    {x y z : obj-Precategory C}
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    ( hom-map-Small-Large-Precategory C D F (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Large-Precategory D
      ( hom-map-Small-Large-Precategory C D F g)
      ( hom-map-Small-Large-Precategory C D F f))

  preserves-id-hom-map-Small-Large-Precategory : UU (l1 ⊔ β γ γ)
  preserves-id-hom-map-Small-Large-Precategory =
    (x : obj-Precategory C) →
    ( hom-map-Small-Large-Precategory C D F (id-hom-Precategory C {x})) ＝
    ( id-hom-Large-Precategory D {γ} {obj-map-Small-Large-Precategory C D F x})

  is-functor-map-Small-Large-Precategory : UU (l1 ⊔ l2 ⊔ β γ γ)
  is-functor-map-Small-Large-Precategory =
    preserves-comp-hom-map-Small-Large-Precategory ×
    preserves-id-hom-map-Small-Large-Precategory

  preserves-comp-is-functor-map-Small-Large-Precategory :
    is-functor-map-Small-Large-Precategory →
    preserves-comp-hom-map-Small-Large-Precategory
  preserves-comp-is-functor-map-Small-Large-Precategory = pr1

  preserves-id-is-functor-map-Small-Large-Precategory :
    is-functor-map-Small-Large-Precategory →
    preserves-id-hom-map-Small-Large-Precategory
  preserves-id-is-functor-map-Small-Large-Precategory = pr2
```

### Functors from small to large precategories

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  where

  functor-Small-Large-Precategory :
    (γ : Level) → UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  functor-Small-Large-Precategory γ =
    functor-Precategory C (precategory-Large-Precategory D γ)

module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  {γ : Level} (F : functor-Small-Large-Precategory C D γ)
  where

  obj-functor-Small-Large-Precategory :
    obj-Precategory C → obj-Large-Precategory D γ
  obj-functor-Small-Large-Precategory =
    obj-functor-Precategory C (precategory-Large-Precategory D γ) F

  hom-functor-Small-Large-Precategory :
    {x y : obj-Precategory C} →
    (f : hom-Precategory C x y) →
    hom-Large-Precategory D
      ( obj-functor-Small-Large-Precategory x)
      ( obj-functor-Small-Large-Precategory y)
  hom-functor-Small-Large-Precategory =
    hom-functor-Precategory C (precategory-Large-Precategory D γ) F

  map-functor-Small-Large-Precategory :
    map-Small-Large-Precategory C D γ
  map-functor-Small-Large-Precategory =
    map-functor-Precategory C (precategory-Large-Precategory D γ) F

  is-functor-functor-Small-Large-Precategory :
    is-functor-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory)
  is-functor-functor-Small-Large-Precategory =
    is-functor-functor-Precategory C (precategory-Large-Precategory D γ) F

  preserves-comp-functor-Small-Large-Precategory :
    {x y z : obj-Precategory C}
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    ( hom-functor-Small-Large-Precategory (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Large-Precategory D
      ( hom-functor-Small-Large-Precategory g)
      ( hom-functor-Small-Large-Precategory f))
  preserves-comp-functor-Small-Large-Precategory =
    preserves-comp-is-functor-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory)
      ( is-functor-functor-Small-Large-Precategory)

  preserves-id-functor-Small-Large-Precategory :
    (x : obj-Precategory C) →
    ( hom-functor-Small-Large-Precategory (id-hom-Precategory C {x})) ＝
    ( id-hom-Large-Precategory D {γ} {obj-functor-Small-Large-Precategory x})
  preserves-id-functor-Small-Large-Precategory =
    preserves-id-is-functor-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory)
      ( is-functor-functor-Small-Large-Precategory)
```

## Properties

### Characterizing equality of functors from small to large precategories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  (F G : functor-Small-Large-Precategory C D γ)
  where

  equiv-eq-map-eq-functor-Small-Large-Precategory :
    ( F ＝ G) ≃
    ( map-functor-Small-Large-Precategory C D F ＝
      map-functor-Small-Large-Precategory C D G)
  equiv-eq-map-eq-functor-Small-Large-Precategory =
    equiv-eq-map-eq-functor-Precategory
      C (precategory-Large-Precategory D γ) F G

  eq-map-eq-functor-Small-Large-Precategory :
    (F ＝ G) →
    ( map-functor-Small-Large-Precategory C D F ＝
      map-functor-Small-Large-Precategory C D G)
  eq-map-eq-functor-Small-Large-Precategory =
    map-equiv equiv-eq-map-eq-functor-Small-Large-Precategory

  eq-eq-map-functor-Small-Large-Precategory :
    ( map-functor-Small-Large-Precategory C D F ＝
      map-functor-Small-Large-Precategory C D G) →
    ( F ＝ G)
  eq-eq-map-functor-Small-Large-Precategory =
    map-inv-equiv equiv-eq-map-eq-functor-Small-Large-Precategory

  is-section-eq-eq-map-functor-Small-Large-Precategory :
    ( eq-map-eq-functor-Small-Large-Precategory ∘
      eq-eq-map-functor-Small-Large-Precategory) ~
    id
  is-section-eq-eq-map-functor-Small-Large-Precategory =
    is-section-map-inv-equiv equiv-eq-map-eq-functor-Small-Large-Precategory

  is-retraction-eq-eq-map-functor-Small-Large-Precategory :
    ( eq-eq-map-functor-Small-Large-Precategory ∘
      eq-map-eq-functor-Small-Large-Precategory) ~
    id
  is-retraction-eq-eq-map-functor-Small-Large-Precategory =
    is-retraction-map-inv-equiv equiv-eq-map-eq-functor-Small-Large-Precategory
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  (F G : functor-Small-Large-Precategory C D γ)
  where

  htpy-functor-Small-Large-Precategory : UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  htpy-functor-Small-Large-Precategory =
    htpy-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory C D F)
      ( map-functor-Small-Large-Precategory C D G)

  equiv-htpy-eq-functor-Small-Large-Precategory :
    (F ＝ G) ≃ htpy-functor-Small-Large-Precategory
  equiv-htpy-eq-functor-Small-Large-Precategory =
    equiv-htpy-eq-functor-Precategory
      C (precategory-Large-Precategory D γ) F G

  htpy-eq-functor-Small-Large-Precategory :
    F ＝ G → htpy-functor-Small-Large-Precategory
  htpy-eq-functor-Small-Large-Precategory =
    map-equiv equiv-htpy-eq-functor-Small-Large-Precategory

  eq-htpy-functor-Small-Large-Precategory :
    htpy-functor-Small-Large-Precategory → F ＝ G
  eq-htpy-functor-Small-Large-Precategory =
    map-inv-equiv equiv-htpy-eq-functor-Small-Large-Precategory

  is-section-eq-htpy-functor-Small-Large-Precategory :
    ( htpy-eq-functor-Small-Large-Precategory ∘
      eq-htpy-functor-Small-Large-Precategory) ~
    id
  is-section-eq-htpy-functor-Small-Large-Precategory =
    is-section-map-inv-equiv equiv-htpy-eq-functor-Small-Large-Precategory

  is-retraction-eq-htpy-functor-Small-Large-Precategory :
    ( eq-htpy-functor-Small-Large-Precategory ∘
      htpy-eq-functor-Small-Large-Precategory) ~
    id
  is-retraction-eq-htpy-functor-Small-Large-Precategory =
    is-retraction-map-inv-equiv
      equiv-htpy-eq-functor-Small-Large-Precategory
```

## See also

- [The precategory of functors and natural transformations from small to large precategories](category-theory.precategory-of-functors-from-small-to-large-precategories.md)

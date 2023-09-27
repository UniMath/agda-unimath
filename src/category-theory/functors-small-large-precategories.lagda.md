# Functors from small to large precategories

```agda
module category-theory.functors-small-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.maps-small-large-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [small precategory](category-theory.small-precategories.md)
`C` to a [large precategory](category-theory.large-precategories.md) `D`
consists of:

- a map `C → D` on objects,
- a map `hom x y → hom (F x) (F y)` on morphisms, such that the following
  identities hold:
- `F id_x = id_(F x)`,
- `F (g ∘ f) = F g ∘ F f`.

## Definition

### The predicate of being a functor on maps between precategories

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

  functor-Small-Large-Precategory : (γ : Level) → UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  functor-Small-Large-Precategory γ =
    Σ ( obj-Precategory C → obj-Large-Precategory D γ)
      ( λ F₀ →
        Σ ( {x y : obj-Precategory C}
            (f : hom-Precategory C x y) →
            hom-Large-Precategory D (F₀ x) (F₀ y))
          ( λ F₁ → is-functor-map-Small-Large-Precategory C D (F₀ , F₁)))

module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  (F : functor-Small-Large-Precategory C D γ)
  where

  obj-functor-Small-Large-Precategory :
    obj-Precategory C → obj-Large-Precategory D γ
  obj-functor-Small-Large-Precategory = pr1 F

  hom-functor-Small-Large-Precategory :
    {x y : obj-Precategory C} →
    (f : hom-Precategory C x y) →
    hom-Large-Precategory D
      ( obj-functor-Small-Large-Precategory x)
      ( obj-functor-Small-Large-Precategory y)
  hom-functor-Small-Large-Precategory = pr1 (pr2 F)

  map-functor-Small-Large-Precategory : map-Small-Large-Precategory C D γ
  pr1 map-functor-Small-Large-Precategory = obj-functor-Small-Large-Precategory
  pr2 map-functor-Small-Large-Precategory = hom-functor-Small-Large-Precategory

  is-functor-functor-Small-Large-Precategory :
    is-functor-map-Small-Large-Precategory C D
      ( map-functor-Small-Large-Precategory)
  is-functor-functor-Small-Large-Precategory = pr2 (pr2 F)

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

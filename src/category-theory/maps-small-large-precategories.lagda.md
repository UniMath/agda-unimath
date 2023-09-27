# Maps from small to large precategories

```agda
module category-theory.maps-small-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [small precategory](category-theory.small-precategories.md) `C`
to a [large precategory](category-theory.large-precategories.md) `D` consists
of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F x) (F y)` on morphisms.

## Definition

```agda
module _
  {l1 l2 : Level} {αD : Level → Level} {βD : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory αD βD)
  where

  map-Small-Large-Precategory : (γ : Level) → UU (l1 ⊔ l2 ⊔ αD γ ⊔ βD γ γ)
  map-Small-Large-Precategory γ =
    Σ ( obj-Precategory C → obj-Large-Precategory D γ)
      ( λ F₀ →
        { X Y : obj-Precategory C} →
        hom-Precategory C X Y → hom-Large-Precategory D (F₀ X) (F₀ Y))

  obj-map-Small-Large-Precategory :
    {γ : Level} → map-Small-Large-Precategory γ →
    obj-Precategory C → obj-Large-Precategory D γ
  obj-map-Small-Large-Precategory = pr1

  hom-map-Small-Large-Precategory :
    {γ : Level} →
    (F : map-Small-Large-Precategory γ) →
    { X Y : obj-Precategory C} →
    hom-Precategory C X Y →
    hom-Large-Precategory D
      ( obj-map-Small-Large-Precategory F X)
      ( obj-map-Small-Large-Precategory F Y)
  hom-map-Small-Large-Precategory = pr2
```

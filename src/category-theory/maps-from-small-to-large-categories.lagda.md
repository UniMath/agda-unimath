# Maps from small to large categories

```agda
module category-theory.maps-from-small-to-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.large-categories
open import category-theory.maps-from-small-to-large-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [(small) category](category-theory.categories.md) `C` to a
[large category](category-theory.large-categories.md) `D` consists of:

- a map `F₀ : C → D` on objects at a chosen universe level `γ`,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms.

## Definition

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2) (D : Large-Category α β)
  where

  map-Small-Large-Category : (γ : Level) → UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  map-Small-Large-Category =
    map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)

  obj-map-Small-Large-Category :
    {γ : Level} → map-Small-Large-Category γ →
    obj-Category C → obj-Large-Category D γ
  obj-map-Small-Large-Category {γ} =
    obj-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)

  hom-map-Small-Large-Category :
    {γ : Level} →
    (F : map-Small-Large-Category γ) →
    { X Y : obj-Category C} →
    hom-Category C X Y →
    hom-Large-Category D
      ( obj-map-Small-Large-Category F X)
      ( obj-map-Small-Large-Category F Y)
  hom-map-Small-Large-Category {γ} =
    hom-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
```

## Properties

### Characterization of equality of maps from small to large categories

```agda
module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2) (D : Large-Category α β)
  where

  htpy-map-Small-Large-Category :
    (f g : map-Small-Large-Category C D γ) → UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  htpy-map-Small-Large-Category =
    htpy-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)

  htpy-eq-map-Small-Large-Category :
    (f g : map-Small-Large-Category C D γ) →
    (f ＝ g) → htpy-map-Small-Large-Category f g
  htpy-eq-map-Small-Large-Category =
    htpy-eq-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)

  is-contr-total-htpy-map-Small-Large-Category :
    (f : map-Small-Large-Category C D γ) →
    is-contr
      ( Σ ( map-Small-Large-Category C D γ)
          ( htpy-map-Small-Large-Category f))
  is-contr-total-htpy-map-Small-Large-Category =
    is-contr-total-htpy-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)

  is-equiv-htpy-eq-map-Small-Large-Category :
    (f g : map-Small-Large-Category C D γ) →
    is-equiv (htpy-eq-map-Small-Large-Category f g)
  is-equiv-htpy-eq-map-Small-Large-Category =
    is-equiv-htpy-eq-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)

  equiv-htpy-eq-map-Small-Large-Category :
    (f g : map-Small-Large-Category C D γ) →
    (f ＝ g) ≃ htpy-map-Small-Large-Category f g
  equiv-htpy-eq-map-Small-Large-Category =
    equiv-htpy-eq-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)

  eq-htpy-map-Small-Large-Category :
    (f g : map-Small-Large-Category C D γ) →
    htpy-map-Small-Large-Category f g → (f ＝ g)
  eq-htpy-map-Small-Large-Category =
    eq-htpy-map-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
```

## See also

- [Functors from small to large categories](category-theory.functors-from-small-to-large-categories.md)
- [The category of maps and natural transformations from small to large categories](category-theory.category-of-maps-from-small-to-large-categories.md)

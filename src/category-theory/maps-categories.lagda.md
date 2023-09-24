# Maps between categories

```agda
module category-theory.maps-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.maps-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [category](category-theory.categories.md) `C` to a category `D`
consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms

## Definition

### Maps between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  where

  map-Category : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Category =
    map-Precategory (precategory-Category C) (precategory-Category D)

  obj-map-Category :
    (F : map-Category) → obj-Category C → obj-Category D
  obj-map-Category =
    obj-map-Precategory (precategory-Category C) (precategory-Category D)

  hom-map-Category :
    (F : map-Category)
    {x y : obj-Category C} →
    hom-Category C x y →
    hom-Category D
      ( obj-map-Category F x)
      ( obj-map-Category F y)
  hom-map-Category =
    hom-map-Precategory (precategory-Category C) (precategory-Category D)
```

## Properties

### Characterization of equality of maps between categories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Category l1 l2)
  (D : Category l3 l4)
  where

  coherence-htpy-map-Category :
    (f g : map-Category C D) →
    (obj-map-Category C D f ~ obj-map-Category C D g) →
    UU (l1 ⊔ l2 ⊔ l4)
  coherence-htpy-map-Category =
    coherence-htpy-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  htpy-map-Category :
    (f g : map-Category C D) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-map-Category =
    htpy-map-Precategory (precategory-Category C) (precategory-Category D)

  refl-htpy-map-Category :
    (f : map-Category C D) → htpy-map-Category f f
  refl-htpy-map-Category =
    refl-htpy-map-Precategory (precategory-Category C) (precategory-Category D)

  htpy-eq-map-Category :
    (f g : map-Category C D) → (f ＝ g) → htpy-map-Category f g
  htpy-eq-map-Category =
    htpy-eq-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  is-contr-total-htpy-map-Category :
    (f : map-Category C D) →
    is-contr (Σ (map-Category C D) (htpy-map-Category f))
  is-contr-total-htpy-map-Category =
    is-contr-total-htpy-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  is-equiv-htpy-eq-map-Category :
    (f g : map-Category C D) → is-equiv (htpy-eq-map-Category f g)
  is-equiv-htpy-eq-map-Category =
    is-equiv-htpy-eq-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  equiv-htpy-eq-map-Category :
    (f g : map-Category C D) → (f ＝ g) ≃ htpy-map-Category f g
  equiv-htpy-eq-map-Category =
    equiv-htpy-eq-map-Precategory
      ( precategory-Category C)
      ( precategory-Category D)

  eq-htpy-map-Category :
    (f g : map-Category C D) → htpy-map-Category f g → (f ＝ g)
  eq-htpy-map-Category =
    eq-htpy-map-Precategory (precategory-Category C) (precategory-Category D)
```

## See also

- [Functors between categories](category-theory.functors-categories.md)

# Maps from small to large precategories

```agda
module category-theory.maps-from-small-to-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [(small) precategory](category-theory.precategories.md) `C` to
a [large precategory](category-theory.large-precategories.md) `D` consists of:

- a map `F₀ : C → D` on objects at a chosen universe level `γ`,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms.

## Definition

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  where

  map-Small-Large-Precategory : (γ : Level) → UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  map-Small-Large-Precategory γ =
    map-Precategory C (precategory-Large-Precategory D γ)

  obj-map-Small-Large-Precategory :
    {γ : Level} → map-Small-Large-Precategory γ →
    obj-Precategory C → obj-Large-Precategory D γ
  obj-map-Small-Large-Precategory {γ} =
    obj-map-Precategory C (precategory-Large-Precategory D γ)

  hom-map-Small-Large-Precategory :
    {γ : Level} →
    (F : map-Small-Large-Precategory γ) →
    { X Y : obj-Precategory C} →
    hom-Precategory C X Y →
    hom-Large-Precategory D
      ( obj-map-Small-Large-Precategory F X)
      ( obj-map-Small-Large-Precategory F Y)
  hom-map-Small-Large-Precategory {γ} =
    hom-map-Precategory C (precategory-Large-Precategory D γ)
```

## Properties

### Characterization of equality of maps from small to large precategories

```agda
module _
  {l1 l2 γ : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2) (D : Large-Precategory α β)
  where

  htpy-map-Small-Large-Precategory :
    (f g : map-Small-Large-Precategory C D γ) → UU (l1 ⊔ l2 ⊔ α γ ⊔ β γ γ)
  htpy-map-Small-Large-Precategory =
    htpy-map-Precategory C (precategory-Large-Precategory D γ)

  htpy-eq-map-Small-Large-Precategory :
    (f g : map-Small-Large-Precategory C D γ) →
    (f ＝ g) → htpy-map-Small-Large-Precategory f g
  htpy-eq-map-Small-Large-Precategory =
    htpy-eq-map-Precategory C (precategory-Large-Precategory D γ)

  is-contr-total-htpy-map-Small-Large-Precategory :
    (f : map-Small-Large-Precategory C D γ) →
    is-contr
      ( Σ ( map-Small-Large-Precategory C D γ)
          ( htpy-map-Small-Large-Precategory f))
  is-contr-total-htpy-map-Small-Large-Precategory =
    is-contr-total-htpy-map-Precategory C (precategory-Large-Precategory D γ)

  is-equiv-htpy-eq-map-Small-Large-Precategory :
    (f g : map-Small-Large-Precategory C D γ) →
    is-equiv (htpy-eq-map-Small-Large-Precategory f g)
  is-equiv-htpy-eq-map-Small-Large-Precategory =
    is-equiv-htpy-eq-map-Precategory C (precategory-Large-Precategory D γ)

  equiv-htpy-eq-map-Small-Large-Precategory :
    (f g : map-Small-Large-Precategory C D γ) →
    (f ＝ g) ≃ htpy-map-Small-Large-Precategory f g
  equiv-htpy-eq-map-Small-Large-Precategory =
    equiv-htpy-eq-map-Precategory C (precategory-Large-Precategory D γ)

  eq-htpy-map-Small-Large-Precategory :
    (f g : map-Small-Large-Precategory C D γ) →
    htpy-map-Small-Large-Precategory f g → (f ＝ g)
  eq-htpy-map-Small-Large-Precategory =
    eq-htpy-map-Precategory C (precategory-Large-Precategory D γ)
```

## See also

- [Functors from small to large precategories](category-theory.functors-from-small-to-large-precategories.md)
- [The precategory of maps and natural transformations from small to large precategories](category-theory.precategory-of-maps-from-small-to-large-precategories.md)

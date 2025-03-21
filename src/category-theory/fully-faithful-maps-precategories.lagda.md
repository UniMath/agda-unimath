# Fully faithful maps between precategories

```agda
module category-theory.fully-faithful-maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.faithful-maps-precategories
open import category-theory.full-maps-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.telescopes
open import foundation.universe-levels
```

</details>

## Idea

A [map](category-theory.maps-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is **fully
faithful** if it's an [equivalence](foundation-core.equivalences.md) on
hom-sets, or equivalently, a [full](category-theory.full-maps-precategories.md)
and [faithful](category-theory.faithful-maps-precategories.md) map on
precategories.

## Definition

### The predicate on maps between precategories of being fully faithful

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  is-fully-faithful-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-fully-faithful-map-Precategory =
    (x y : obj-Precategory C) → is-equiv (hom-map-Precategory C D F {x} {y})

  is-prop-is-fully-faithful-map-Precategory :
    is-prop is-fully-faithful-map-Precategory
  is-prop-is-fully-faithful-map-Precategory =
    is-prop-iterated-Π 2
      ( λ x y → is-property-is-equiv (hom-map-Precategory C D F {x} {y}))

  is-fully-faithful-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  pr1 is-fully-faithful-prop-map-Precategory = is-fully-faithful-map-Precategory
  pr2 is-fully-faithful-prop-map-Precategory =
    is-prop-is-fully-faithful-map-Precategory

  equiv-hom-is-fully-faithful-map-Precategory :
    is-fully-faithful-map-Precategory → {x y : obj-Precategory C} →
    hom-Precategory C x y ≃
    hom-Precategory D
      ( obj-map-Precategory C D F x)
      ( obj-map-Precategory C D F y)
  pr1 (equiv-hom-is-fully-faithful-map-Precategory is-ff-F) =
    hom-map-Precategory C D F
  pr2 (equiv-hom-is-fully-faithful-map-Precategory is-ff-F {x} {y}) =
    is-ff-F x y

  inv-equiv-hom-is-fully-faithful-map-Precategory :
    is-fully-faithful-map-Precategory → {x y : obj-Precategory C} →
    hom-Precategory D
      ( obj-map-Precategory C D F x)
      ( obj-map-Precategory C D F y) ≃
    hom-Precategory C x y
  inv-equiv-hom-is-fully-faithful-map-Precategory is-ff-F =
    inv-equiv (equiv-hom-is-fully-faithful-map-Precategory is-ff-F)

  map-inv-hom-is-fully-faithful-map-Precategory :
    is-fully-faithful-map-Precategory → {x y : obj-Precategory C} →
    hom-Precategory D
      ( obj-map-Precategory C D F x)
      ( obj-map-Precategory C D F y) →
    hom-Precategory C x y
  map-inv-hom-is-fully-faithful-map-Precategory is-ff-F =
    map-equiv (inv-equiv-hom-is-fully-faithful-map-Precategory is-ff-F)
```

### The type of fully faithful maps between two precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  fully-faithful-map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fully-faithful-map-Precategory =
    Σ (map-Precategory C D) (is-fully-faithful-map-Precategory C D)

  map-fully-faithful-map-Precategory :
    fully-faithful-map-Precategory → map-Precategory C D
  map-fully-faithful-map-Precategory = pr1

  is-fully-faithful-fully-faithful-map-Precategory :
    (F : fully-faithful-map-Precategory) →
    is-fully-faithful-map-Precategory C D (map-fully-faithful-map-Precategory F)
  is-fully-faithful-fully-faithful-map-Precategory = pr2

  obj-fully-faithful-map-Precategory :
    fully-faithful-map-Precategory → obj-Precategory C → obj-Precategory D
  obj-fully-faithful-map-Precategory =
    obj-map-Precategory C D ∘ map-fully-faithful-map-Precategory

  hom-fully-faithful-map-Precategory :
    (F : fully-faithful-map-Precategory) {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-fully-faithful-map-Precategory F x)
      ( obj-fully-faithful-map-Precategory F y)
  hom-fully-faithful-map-Precategory =
    hom-map-Precategory C D ∘ map-fully-faithful-map-Precategory

  equiv-hom-fully-faithful-map-Precategory :
    (F : fully-faithful-map-Precategory) {x y : obj-Precategory C} →
    hom-Precategory C x y ≃
    hom-Precategory D
      ( obj-fully-faithful-map-Precategory F x)
      ( obj-fully-faithful-map-Precategory F y)
  equiv-hom-fully-faithful-map-Precategory F =
    equiv-hom-is-fully-faithful-map-Precategory C D
      ( map-fully-faithful-map-Precategory F)
      ( is-fully-faithful-fully-faithful-map-Precategory F)

  inv-equiv-hom-fully-faithful-map-Precategory :
    (F : fully-faithful-map-Precategory) {x y : obj-Precategory C} →
    hom-Precategory D
      ( obj-fully-faithful-map-Precategory F x)
      ( obj-fully-faithful-map-Precategory F y) ≃
    hom-Precategory C x y
  inv-equiv-hom-fully-faithful-map-Precategory F =
    inv-equiv (equiv-hom-fully-faithful-map-Precategory F)

  map-inv-hom-fully-faithful-map-Precategory :
    (F : fully-faithful-map-Precategory) {x y : obj-Precategory C} →
    hom-Precategory D
      ( obj-fully-faithful-map-Precategory F x)
      ( obj-fully-faithful-map-Precategory F y) →
    hom-Precategory C x y
  map-inv-hom-fully-faithful-map-Precategory F =
    map-equiv (inv-equiv-hom-fully-faithful-map-Precategory F)
```

## Properties

### Fully faithful maps are the same as full and faithful maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  is-full-is-fully-faithful-map-Precategory :
    is-fully-faithful-map-Precategory C D F → is-full-map-Precategory C D F
  is-full-is-fully-faithful-map-Precategory is-ff-F x y =
    is-surjective-is-equiv (is-ff-F x y)

  full-map-is-fully-faithful-map-Precategory :
    is-fully-faithful-map-Precategory C D F → full-map-Precategory C D
  pr1 (full-map-is-fully-faithful-map-Precategory is-ff-F) = F
  pr2 (full-map-is-fully-faithful-map-Precategory is-ff-F) =
    is-full-is-fully-faithful-map-Precategory is-ff-F

  is-faithful-is-fully-faithful-map-Precategory :
    is-fully-faithful-map-Precategory C D F → is-faithful-map-Precategory C D F
  is-faithful-is-fully-faithful-map-Precategory is-ff-F x y =
    is-emb-is-equiv (is-ff-F x y)

  faithful-map-is-fully-faithful-map-Precategory :
    is-fully-faithful-map-Precategory C D F → faithful-map-Precategory C D
  pr1 (faithful-map-is-fully-faithful-map-Precategory is-ff-F) = F
  pr2 (faithful-map-is-fully-faithful-map-Precategory is-ff-F) =
    is-faithful-is-fully-faithful-map-Precategory is-ff-F

  is-fully-faithful-is-full-is-faithful-map-Precategory :
    is-full-map-Precategory C D F →
    is-faithful-map-Precategory C D F →
    is-fully-faithful-map-Precategory C D F
  is-fully-faithful-is-full-is-faithful-map-Precategory
    is-full-F is-faithful-F x y =
    is-equiv-is-emb-is-surjective (is-full-F x y) (is-faithful-F x y)

  fully-faithful-map-is-full-is-faithful-map-Precategory :
    is-full-map-Precategory C D F →
    is-faithful-map-Precategory C D F →
    fully-faithful-map-Precategory C D
  pr1
    ( fully-faithful-map-is-full-is-faithful-map-Precategory
      is-full-F is-faithful-F) =
    F
  pr2
    ( fully-faithful-map-is-full-is-faithful-map-Precategory
      is-full-F is-faithful-F) =
    is-fully-faithful-is-full-is-faithful-map-Precategory
      ( is-full-F) (is-faithful-F)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : fully-faithful-map-Precategory C D)
  where

  full-map-fully-faithful-map-Precategory : full-map-Precategory C D
  full-map-fully-faithful-map-Precategory =
    full-map-is-fully-faithful-map-Precategory C D
      ( map-fully-faithful-map-Precategory C D F)
      ( is-fully-faithful-fully-faithful-map-Precategory C D F)

  faithful-map-fully-faithful-map-Precategory : faithful-map-Precategory C D
  faithful-map-fully-faithful-map-Precategory =
    faithful-map-is-fully-faithful-map-Precategory C D
      ( map-fully-faithful-map-Precategory C D F)
      ( is-fully-faithful-fully-faithful-map-Precategory C D F)
```

## See also

- [Fully faithful functors between precategories](category-theory.fully-faithful-functors-precategories.md)

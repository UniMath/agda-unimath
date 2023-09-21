# Maps between precategories

```agda
module category-theory.maps-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [precategory](category-theory.precategories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms

## Definition

### Maps between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  map-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Precategory =
    Σ ( obj-Precategory C → obj-Precategory D)
      ( λ F₀ →
        {x y : obj-Precategory C} →
        hom-Precategory C x y →
        hom-Precategory D (F₀ x) (F₀ y))

  map-obj-map-Precategory :
    (F : map-Precategory) → obj-Precategory C → obj-Precategory D
  map-obj-map-Precategory = pr1

  map-hom-map-Precategory :
    (F : map-Precategory)
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( map-obj-map-Precategory F x)
      ( map-obj-map-Precategory F y)
  map-hom-map-Precategory = pr2
```

## See also

- [Functors between precategories](category-theory.functors-precategories.md)

# Maps between nonunital precategories

```agda
module category-theory.maps-nonunital-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-set-magmoids
open import category-theory.nonunital-precategories

open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

A **map** from a [nonunital precategory](category-theory.precategories.md) `C`
to a nonunital precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms

## Definitions

### Maps between nonunital precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Nonunital-Precategory l1 l2)
  (D : Nonunital-Precategory l3 l4)
  where

  map-Nonunital-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Nonunital-Precategory =
    Σ ( obj-Nonunital-Precategory C → obj-Nonunital-Precategory D)
      ( λ F₀ →
        {x y : obj-Nonunital-Precategory C} →
        hom-Nonunital-Precategory C x y →
        hom-Nonunital-Precategory D (F₀ x) (F₀ y))

  obj-map-Nonunital-Precategory :
    (F : map-Nonunital-Precategory) →
    obj-Nonunital-Precategory C →
    obj-Nonunital-Precategory D
  obj-map-Nonunital-Precategory = pr1

  hom-map-Nonunital-Precategory :
    (F : map-Nonunital-Precategory)
    {x y : obj-Nonunital-Precategory C} →
    hom-Nonunital-Precategory C x y →
    hom-Nonunital-Precategory D
      ( obj-map-Nonunital-Precategory F x)
      ( obj-map-Nonunital-Precategory F y)
  hom-map-Nonunital-Precategory = pr2
```

## See also

- [Functors between nonunital precategories](category-theory.functors-nonunital-precategories.md)
- [The precategory of maps and natural transformations between nonunital precategories](category-theory.precategory-of-maps-nonunital-precategories.md)

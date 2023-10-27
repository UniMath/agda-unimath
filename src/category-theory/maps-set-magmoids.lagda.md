# Maps between set magmoids

```agda
module category-theory.maps-set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-set-magmoids
open import category-theory.set-magmoids

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

A **map** from a [set magmoid](category-theory.set-magmoids.md) `C` to a set
magmoid `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms

## Definitions

### Maps between set magmoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Set-Magmoid l1 l2)
  (D : Set-Magmoid l3 l4)
  where

  map-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Set-Magmoid =
    Σ ( obj-Set-Magmoid C → obj-Set-Magmoid D)
      ( λ F₀ →
        {x y : obj-Set-Magmoid C} →
        hom-Set-Magmoid C x y →
        hom-Set-Magmoid D (F₀ x) (F₀ y))

  obj-map-Set-Magmoid :
    (F : map-Set-Magmoid) →
    obj-Set-Magmoid C →
    obj-Set-Magmoid D
  obj-map-Set-Magmoid = pr1

  hom-map-Set-Magmoid :
    (F : map-Set-Magmoid)
    {x y : obj-Set-Magmoid C} →
    hom-Set-Magmoid C x y →
    hom-Set-Magmoid D
      ( obj-map-Set-Magmoid F x)
      ( obj-map-Set-Magmoid F y)
  hom-map-Set-Magmoid = pr2
```

## See also

- [Functors between set magmoids](category-theory.functors-set-magmoids.md)
- [The precategory of maps and natural transformations between set magmoids](category-theory.precategory-of-maps-set-magmoids.md)

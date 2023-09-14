# Representations of monoids in categories

```agda
module group-theory.representations-monoids-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.endomorphisms-in-categories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.representations-monoids-precategories
```

</details>

## Idea

A **representation** of a [monoid](group-theory.monoids.md) `M` in a
[category](category-theory.categories.md) `C` consist of an object `V` in `C`
[equipped](foundation.structure.md) with a
[monoid homomorphism](group-theory.homomorphisms-monoids.md) from `M` to the
monoid of [endomorphisms](category-theory.endomorphisms-in-categories.md) on
`V`.

## Definition

### Representations of a monoid in a category

```agda
representation-category-Monoid :
  {l1 l2 l3 : Level} (M : Monoid l1) (C : Category l2 l3) → UU (l1 ⊔ l2 ⊔ l3)
representation-category-Monoid M C =
  representation-precategory-Monoid M (precategory-Category C)

module _
  {l1 l2 l3 : Level} (M : Monoid l1) (C : Category l2 l3)
  (ρ : representation-category-Monoid M C)
  where

  obj-representation-category-Monoid : obj-Category C
  obj-representation-category-Monoid =
    obj-representation-precategory-Monoid M (precategory-Category C) ρ

  hom-action-representation-category-Monoid :
    type-hom-Monoid M
      ( monoid-endo-Category C obj-representation-category-Monoid)
  hom-action-representation-category-Monoid =
    hom-action-representation-precategory-Monoid M (precategory-Category C) ρ

  action-representation-category-Monoid :
    type-Monoid M → type-endo-Category C obj-representation-category-Monoid
  action-representation-category-Monoid =
    action-representation-precategory-Monoid M (precategory-Category C) ρ

  preserves-mul-action-representation-category-Monoid :
    ( x y : type-Monoid M) →
    ( action-representation-category-Monoid (mul-Monoid M x y)) ＝
    ( comp-endo-Category C
      ( obj-representation-category-Monoid)
      ( action-representation-category-Monoid x)
      ( action-representation-category-Monoid y))
  preserves-mul-action-representation-category-Monoid =
    preserves-mul-action-representation-precategory-Monoid M
      ( precategory-Category C)
      ( ρ)

  preserves-unit-action-representation-category-Monoid :
    action-representation-category-Monoid (unit-Monoid M) ＝
    id-endo-Category C obj-representation-category-Monoid
  preserves-unit-action-representation-category-Monoid =
    preserves-unit-action-representation-precategory-Monoid M
      ( precategory-Category C)
      ( ρ)
```

### The type of representations of a monoid

```agda
Representation-Category-Monoid :
  {l1 : Level} (M : Monoid l1) (l2 l3 : Level) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Representation-Category-Monoid M l2 l3 =
  Σ (Category l2 l3) (representation-category-Monoid M)

module _
  {l1 l2 l3 : Level} (M : Monoid l1)
  (ρ : Representation-Category-Monoid M l2 l3)
  where

  category-Representation-Category-Monoid : Category l2 l3
  category-Representation-Category-Monoid = pr1 ρ

  representation-category-Representation-Category-Monoid :
    representation-category-Monoid M
      ( category-Representation-Category-Monoid)
  representation-category-Representation-Category-Monoid = pr2 ρ

  obj-Representation-Category-Monoid :
    obj-Category category-Representation-Category-Monoid
  obj-Representation-Category-Monoid =
    obj-representation-category-Monoid M
      ( category-Representation-Category-Monoid)
      ( representation-category-Representation-Category-Monoid)

  hom-action-Representation-Category-Monoid :
    type-hom-Monoid M
      ( monoid-endo-Category
        ( category-Representation-Category-Monoid)
        ( obj-Representation-Category-Monoid))
  hom-action-Representation-Category-Monoid =
    hom-action-representation-category-Monoid M
      ( category-Representation-Category-Monoid)
      ( representation-category-Representation-Category-Monoid)

  action-Representation-Category-Monoid :
    type-Monoid M →
    type-endo-Category
      ( category-Representation-Category-Monoid)
      ( obj-Representation-Category-Monoid)
  action-Representation-Category-Monoid =
    action-representation-category-Monoid M
      ( category-Representation-Category-Monoid)
      ( representation-category-Representation-Category-Monoid)

  preserves-mul-action-Representation-Category-Monoid :
    ( x y : type-Monoid M) →
    ( action-Representation-Category-Monoid (mul-Monoid M x y)) ＝
    ( comp-endo-Category
      ( category-Representation-Category-Monoid)
      ( obj-Representation-Category-Monoid)
      ( action-Representation-Category-Monoid x)
      ( action-Representation-Category-Monoid y))
  preserves-mul-action-Representation-Category-Monoid =
    preserves-mul-action-representation-category-Monoid M
      ( category-Representation-Category-Monoid)
      ( representation-category-Representation-Category-Monoid)

  preserves-unit-action-Representation-Category-Monoid :
    action-Representation-Category-Monoid (unit-Monoid M) ＝
    id-endo-Category
      ( category-Representation-Category-Monoid)
      ( obj-Representation-Category-Monoid)
  preserves-unit-action-Representation-Category-Monoid =
    preserves-unit-action-representation-category-Monoid M
      ( category-Representation-Category-Monoid)
      ( representation-category-Representation-Category-Monoid)
```

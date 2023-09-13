# Representations of monoids

```agda
module group-theory.representations-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.endomorphisms-in-categories

open import foundation.dependent-pair-types
open import foundation.endomorphisms
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids

open import structured-types.morphisms-wild-monoids
open import structured-types.wild-monoids
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
  {l1 l2 l3 : Level} (C : Category l1 l2) (M : Monoid l3) → UU (l1 ⊔ l2 ⊔ l3)
representation-category-Monoid C M =
  Σ (obj-Category C) (λ V → type-hom-Monoid M (monoid-endo-Category C V))

module _
  {l1 l2 l3 : Level} (C : Category l1 l2) (M : Monoid l3)
  (ρ : representation-category-Monoid C M)
  where

  obj-representation-category-Monoid : obj-Category C
  obj-representation-category-Monoid = pr1 ρ

  hom-action-representation-category-Monoid :
    type-hom-Monoid M
      ( monoid-endo-Category C obj-representation-category-Monoid)
  hom-action-representation-category-Monoid = pr2 ρ

  action-representation-category-Monoid :
    type-Monoid M → type-endo-Category C obj-representation-category-Monoid
  action-representation-category-Monoid =
    map-hom-Monoid M
      ( monoid-endo-Category C obj-representation-category-Monoid)
      ( hom-action-representation-category-Monoid)

  preserves-mul-action-representation-category-Monoid :
    ( x y : type-Monoid M) →
    ( action-representation-category-Monoid (mul-Monoid M x y)) ＝
    ( comp-endo-Category C
      ( obj-representation-category-Monoid)
      ( action-representation-category-Monoid x)
      ( action-representation-category-Monoid y))
  preserves-mul-action-representation-category-Monoid =
    preserves-mul-hom-Monoid M
      ( monoid-endo-Category C obj-representation-category-Monoid)
      ( hom-action-representation-category-Monoid)

  preserves-unit-action-representation-category-Monoid :
    action-representation-category-Monoid (unit-Monoid M) ＝
    id-endo-Category C obj-representation-category-Monoid
  preserves-unit-action-representation-category-Monoid =
    preserves-unit-hom-Monoid M
      ( monoid-endo-Category C obj-representation-category-Monoid)
      ( hom-action-representation-category-Monoid)
```

# Representations of monoids in precategories

```agda
module group-theory.representations-monoids-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.endomorphisms-in-precategories
open import category-theory.functors-precategories
open import category-theory.one-object-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.monoids
```

</details>

## Idea

A **representation** of a [monoid](group-theory.monoids.md) `M` in a
[precategory](category-theory.precategories.md) `C` consist of an object `V` in
`C` [equipped](foundation.structure.md) with a
[monoid homomorphism](group-theory.homomorphisms-monoids.md) from `M` to the
monoid of [endomorphisms](category-theory.endomorphisms-in-precategories.md) on
`V`. However, since
[monoids are one-object precategories](category-theory.one-object-precategories.md),
we can encode this as a functor of categories `M → C`.

## Definition

### Representations of a monoid in a precategory

```agda
representation-precategory-Monoid :
  {l1 l2 l3 : Level} (M : Monoid l1) (C : Precategory l2 l3) → UU (l1 ⊔ l2 ⊔ l3)
representation-precategory-Monoid M C =
  functor-Precategory (precategory-one-object-precategory-Monoid M) C

module _
  {l1 l2 l3 : Level} (M : Monoid l1) (C : Precategory l2 l3)
  (ρ : representation-precategory-Monoid M C)
  where

  obj-representation-precategory-Monoid : obj-Precategory C
  obj-representation-precategory-Monoid = pr1 ρ star

  action-representation-precategory-Monoid :
    type-Monoid M →
    type-endo-Precategory C obj-representation-precategory-Monoid
  action-representation-precategory-Monoid = pr1 (pr2 ρ)

  preserves-mul-action-representation-precategory-Monoid :
    ( x y : type-Monoid M) →
    ( action-representation-precategory-Monoid (mul-Monoid M x y)) ＝
    ( comp-endo-Precategory C
      ( obj-representation-precategory-Monoid)
      ( action-representation-precategory-Monoid x)
      ( action-representation-precategory-Monoid y))
  preserves-mul-action-representation-precategory-Monoid =
    preserves-comp-functor-Precategory
      ( precategory-one-object-precategory-Monoid M) C ρ

  preserves-unit-action-representation-precategory-Monoid :
    action-representation-precategory-Monoid (unit-Monoid M) ＝
    id-endo-Precategory C obj-representation-precategory-Monoid
  preserves-unit-action-representation-precategory-Monoid =
    preserves-id-functor-Precategory
      ( precategory-one-object-precategory-Monoid M) C ρ star
```

### The total type of representations of a monoid

```agda
Representation-Precategory-Monoid :
  {l1 : Level} (M : Monoid l1) (l2 l3 : Level) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Representation-Precategory-Monoid M l2 l3 =
  Σ (Precategory l2 l3) (representation-precategory-Monoid M)

module _
  {l1 l2 l3 : Level} (M : Monoid l1)
  (ρ : Representation-Precategory-Monoid M l2 l3)
  where

  precategory-Representation-Precategory-Monoid : Precategory l2 l3
  precategory-Representation-Precategory-Monoid = pr1 ρ

  representation-precategory-Representation-Precategory-Monoid :
    representation-precategory-Monoid M
      ( precategory-Representation-Precategory-Monoid)
  representation-precategory-Representation-Precategory-Monoid = pr2 ρ

  obj-Representation-Precategory-Monoid :
    obj-Precategory precategory-Representation-Precategory-Monoid
  obj-Representation-Precategory-Monoid =
    obj-representation-precategory-Monoid M
      ( precategory-Representation-Precategory-Monoid)
      ( representation-precategory-Representation-Precategory-Monoid)

  action-Representation-Precategory-Monoid :
    type-Monoid M →
    type-endo-Precategory
      ( precategory-Representation-Precategory-Monoid)
      ( obj-Representation-Precategory-Monoid)
  action-Representation-Precategory-Monoid =
    action-representation-precategory-Monoid M
      ( precategory-Representation-Precategory-Monoid)
      ( representation-precategory-Representation-Precategory-Monoid)

  preserves-mul-action-Representation-Precategory-Monoid :
    ( x y : type-Monoid M) →
    ( action-Representation-Precategory-Monoid (mul-Monoid M x y)) ＝
    ( comp-endo-Precategory
      ( precategory-Representation-Precategory-Monoid)
      ( obj-Representation-Precategory-Monoid)
      ( action-Representation-Precategory-Monoid x)
      ( action-Representation-Precategory-Monoid y))
  preserves-mul-action-Representation-Precategory-Monoid =
    preserves-mul-action-representation-precategory-Monoid M
      ( precategory-Representation-Precategory-Monoid)
      ( representation-precategory-Representation-Precategory-Monoid)

  preserves-unit-action-Representation-Precategory-Monoid :
    action-Representation-Precategory-Monoid (unit-Monoid M) ＝
    id-endo-Precategory
      ( precategory-Representation-Precategory-Monoid)
      ( obj-Representation-Precategory-Monoid)
  preserves-unit-action-Representation-Precategory-Monoid =
    preserves-unit-action-representation-precategory-Monoid M
      ( precategory-Representation-Precategory-Monoid)
      ( representation-precategory-Representation-Precategory-Monoid)
```

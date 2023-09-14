# Concrete monoids

```agda
module group-theory.concrete-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.endomorphisms-in-precategories
open import category-theory.precategories

open import foundation.0-connected-types
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.cores-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.torsors

open import structured-types.pointed-types
```

</details>

## Idea

A **concrete monoid**, or **univalent monoid**, is the homotopy type theoretic
analogue of [monoids](group-theory.monoids.md). We define it as a
[category](category-theory.categories.md) whose type of objects is
[pointed](structured-types.pointed-types.md) and
[connected](foundation.0-connected-types.md).

## Definition

```agda
is-concrete-monoid-Category : {l1 l2 : Level} → Category l1 l2 → UU l1
is-concrete-monoid-Category C =
  obj-Category C × is-0-connected (obj-Category C)

Concrete-Monoid : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Concrete-Monoid l1 l2 = Σ (Category l1 l2) (is-concrete-monoid-Category)

module _
  {l1 l2 : Level} (M : Concrete-Monoid l1 l2)
  where

  category-Concrete-Monoid : Category l1 l2
  category-Concrete-Monoid = pr1 M

  is-concrete-monoid-category-Concrete-Monoid :
    is-concrete-monoid-Category category-Concrete-Monoid
  is-concrete-monoid-category-Concrete-Monoid = pr2 M
```

## Properties

### Concrete monoids from monoids

From a monoid, we can define its associated concrete monoid. The type of objects
is the classifying type of the core of the monoid. Moreover, we must take care
in how we define the family of homomorphism sets. They cannot simply be the
constant family.

```agda
module _
  {l : Level} (M : Monoid l)
  where

  obj-concrete-monoid-Monoid : UU (lsuc l)
  obj-concrete-monoid-Monoid = classifying-type-Group (group-core-Monoid M)

  hom-concrete-monoid-Monoid :
    obj-concrete-monoid-Monoid → obj-concrete-monoid-Monoid → Set {!   !}
  hom-concrete-monoid-Monoid x y = {!   !}

  precategory-concrete-monoid-Monoid : Precategory {!   !} {!   !}
  pr1 precategory-concrete-monoid-Monoid = {!   !}
  pr2 precategory-concrete-monoid-Monoid = {!   !}

  concrete-monoid-Monoid : Concrete-Monoid {!   !} {!   !}
  pr1 concrete-monoid-Monoid = {!   !}
  pr2 concrete-monoid-Monoid = {!   !}
```

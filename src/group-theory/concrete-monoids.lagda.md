# Concrete monoids

```agda
module group-theory.concrete-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.endomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.categories

open import foundation.contractible-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.0-connected-types
open import structured-types.pointed-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

A **concrete monoid**, or **univalent monoid**, is the homotopy type theoretic
analogue of [monoids](group-theory.monoids.md). We define it as a
[category](category-theory.categories.md) whose type of objects is
[pointed](structured-types.pointed-types.md) and
[connected](foundation.connected-types.md).

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

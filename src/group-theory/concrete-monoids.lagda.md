# Concrete monoids

```agda
module group-theory.concrete-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories

open import foundation.0-connected-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.cores-monoids
open import group-theory.monoids
open import group-theory.torsors
```

</details>

## Idea

A **concrete monoid**, or **univalent monoid**, is the homotopy type theoretic
analog of [monoids](group-theory.monoids.md). We define it as a
[category](category-theory.categories.md) whose type of objects is
[pointed](structured-types.pointed-types.md) and
[connected](foundation.0-connected-types.md).

## Definition

```agda
is-concrete-monoid-Category : {l1 l2 : Level} → Category l1 l2 → UU l1
is-concrete-monoid-Category C = obj-Category C × is-0-connected (obj-Category C)

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

Given a monoid, we can define its associated concrete monoid. The type of
objects is the [classifying type](group-theory.concrete-groups.md) of the
[core](group-theory.cores-monoids.md) of the monoid. Moreover, we must take care
in how we define the family of homomorphisms. They cannot simply be the constant
family, as [transporting along](foundation.transport-along-identifications.md)
an [invertible element](group-theory.invertible-elements-monoids.md) should
correspond to multiplying by the element in the family.

```agda
module _
  {l : Level} (M : Monoid l)
  where

  obj-concrete-monoid-Monoid : UU (lsuc l)
  obj-concrete-monoid-Monoid = classifying-type-Group (core-Monoid M)
```

The remainder of the construction remains to be written down. We note that this
is precisely the Rezk completion of the one object precategory associated to a
monoid.

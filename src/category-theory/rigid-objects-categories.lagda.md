# Rigid objects in a category

```agda
module category-theory.rigid-objects-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.rigid-objects-precategories

open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A **rigid object** in a [category](category-theory.categories.md) is an object
whose [automorphism group](group-theory.automorphism-groups.md) is
[trivial](group-theory.trivial-groups.md).

## Definitions

### The predicate of being rigid

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2) (x : obj-Category C)
  where

  is-rigid-obj-prop-Category : Prop l2
  is-rigid-obj-prop-Category =
    is-rigid-obj-prop-Precategory (precategory-Category C) x

  is-rigid-obj-Category : UU l2
  is-rigid-obj-Category = type-Prop is-rigid-obj-prop-Category

  is-prop-is-rigid-obj-Category : is-prop is-rigid-obj-Category
  is-prop-is-rigid-obj-Category =
    is-prop-type-Prop is-rigid-obj-prop-Category
```

### The type of rigid objects in a category

```agda
rigid-obj-Category : {l1 l2 : Level} (C : Category l1 l2) → UU (l1 ⊔ l2)
rigid-obj-Category C =
    rigid-obj-Precategory (precategory-Category C)

module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  obj-rigid-obj-Category : rigid-obj-Category C → obj-Category C
  obj-rigid-obj-Category = obj-rigid-obj-Precategory (precategory-Category C)

  is-rigid-rigid-obj-Category :
    (x : rigid-obj-Category C) →
    is-rigid-obj-Category C (obj-rigid-obj-Category x)
  is-rigid-rigid-obj-Category =
    is-rigid-rigid-obj-Precategory (precategory-Category C)
```

## See also

- Every object in a category is rigid if and only if it is
  [gaunt](category-theory.gaunt-categories.md).

## External links

- [rigid object](https://ncatlab.org/nlab/show/rigid+object) at $n$Lab

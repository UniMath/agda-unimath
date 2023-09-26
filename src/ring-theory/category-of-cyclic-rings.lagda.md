# The category of cyclic rings

```agda
module ring-theory.category-of-cyclic-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-categories
open import category-theory.large-precategories

open import foundation.fundamental-theorem-of-identity-types
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import order-theory.large-posets

open import ring-theory.cyclic-rings
open import ring-theory.homomorphisms-cyclic-rings
open import ring-theory.isomorphisms-rings
```

</details>

## Idea

The **large category of cyclic rings** is the
[large category](category-theory.large-categories.md) consisting of
[cyclic rings](ring-theory.cyclic-rings.md) and
[ring homomorphisms](ring-theory.homomorphisms-cyclic-rings.md).

Note that we already showed that there is at most one ring homomorphism between
any two cyclic rings, so it follows that the large category of cyclic rings is
in fact a [large poset](order-theory.large-posets.md). The large poset of cyclic
rings is constructed in the file
[`ring-theory.poset-of-cyclic-rings`](ring-theory.poset-of-cyclic-rings.md).

## Definition

### The large precategory of cyclic rings

```agda
Cyclic-Ring-Large-Precategory : Large-Precategory lsuc _⊔_
obj-Large-Precategory
  Cyclic-Ring-Large-Precategory =
  Cyclic-Ring
hom-set-Large-Precategory
  Cyclic-Ring-Large-Precategory =
  hom-set-Cyclic-Ring
comp-hom-Large-Precategory
  Cyclic-Ring-Large-Precategory {X = R} {Y = S} {Z = T} =
  comp-hom-Cyclic-Ring R S T
id-hom-Large-Precategory
  Cyclic-Ring-Large-Precategory {X = R} =
  id-hom-Cyclic-Ring R
associative-comp-hom-Large-Precategory
  Cyclic-Ring-Large-Precategory {X = R} {Y = S} {Z = T} {W = U} =
  associative-comp-hom-Cyclic-Ring R S T U
left-unit-law-comp-hom-Large-Precategory
  Cyclic-Ring-Large-Precategory {X = R} {Y = S} =
  left-unit-law-comp-hom-Cyclic-Ring R S
right-unit-law-comp-hom-Large-Precategory
  Cyclic-Ring-Large-Precategory {X = R} {Y = S} =
  right-unit-law-comp-hom-Cyclic-Ring R S
```

### The large category of cyclic rings

```agda
abstract
  is-large-category-Cyclic-Ring-Large-Category :
    is-large-category-Large-Precategory Cyclic-Ring-Large-Precategory
  is-large-category-Cyclic-Ring-Large-Category R =
    fundamental-theorem-id
      ( is-contr-total-Eq-subtype
        ( is-contr-total-iso-Ring (ring-Cyclic-Ring R))
        ( is-prop-is-cyclic-Ring)
        ( ring-Cyclic-Ring R)
        ( id-iso-Ring (ring-Cyclic-Ring R))
        ( is-cyclic-Cyclic-Ring R))
      ( iso-eq-Large-Precategory Cyclic-Ring-Large-Precategory R)

Cyclic-Ring-Large-Category : Large-Category lsuc _⊔_
large-precategory-Large-Category
  Cyclic-Ring-Large-Category =
  Cyclic-Ring-Large-Precategory
is-large-category-Large-Category
  Cyclic-Ring-Large-Category =
  is-large-category-Cyclic-Ring-Large-Category
```

### The small categories of cyclic rings

```agda
Cyclic-Ring-Category : (l : Level) → Category (lsuc l) l
Cyclic-Ring-Category = category-Large-Category Cyclic-Ring-Large-Category
```

## Properties

### The large category of cyclic rings is a large poset

```agda
is-large-poset-Cyclic-Ring-Large-Category :
  is-large-poset-Large-Category Cyclic-Ring-Large-Category
is-large-poset-Cyclic-Ring-Large-Category =
  is-prop-hom-Cyclic-Ring
```

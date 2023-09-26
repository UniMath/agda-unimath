# The precategory of semigroups

```agda
module group-theory.precategory-of-semigroups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
```

</details>

## Idea

Semigroups and semigroup homomorphisms form a precategory.

## Definition

### The precategory of semigroups

```agda
instance
  Semigroup-Large-Precategory : Large-Precategory lsuc (_⊔_)
  obj-Large-Precategory Semigroup-Large-Precategory = Semigroup
  hom-set-Large-Precategory Semigroup-Large-Precategory = hom-set-Semigroup
  comp-hom-Large-Precategory Semigroup-Large-Precategory
    {X = G} {H} {K} =
    comp-hom-Semigroup G H K
  id-hom-Large-Precategory Semigroup-Large-Precategory
    {X = G} =
    id-hom-Semigroup G
  associative-comp-hom-Large-Precategory Semigroup-Large-Precategory
    {X = G} {H} {K} {L} =
    associative-comp-hom-Semigroup G H K L
  left-unit-law-comp-hom-Large-Precategory Semigroup-Large-Precategory
    {X = G} {H} =
    left-unit-law-comp-hom-Semigroup G H
  right-unit-law-comp-hom-Large-Precategory Semigroup-Large-Precategory
    {X = G} {H} =
    right-unit-law-comp-hom-Semigroup G H
```

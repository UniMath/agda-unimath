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
  Semigroup-Large-Precat : Large-Precat lsuc (_⊔_)
  obj-Large-Precat Semigroup-Large-Precat = Semigroup
  hom-Large-Precat Semigroup-Large-Precat = hom-Semigroup
  compose-hom-Large-Precat Semigroup-Large-Precat
    {X = G} {H} {K} =
    compose-hom-Semigroup G H K
  id-hom-Large-Precat Semigroup-Large-Precat
    {X = G} =
    id-hom-Semigroup G
  assoc-compose-hom-Large-Precat Semigroup-Large-Precat
    {X = G} {H} {K} {L} =
    assoc-compose-hom-Semigroup G H K L
  left-unit-law-compose-hom-Large-Precat Semigroup-Large-Precat
    {X = G} {H} =
    left-unit-law-compose-hom-Semigroup G H
  right-unit-law-compose-hom-Large-Precat Semigroup-Large-Precat
    {X = G} {H} =
    right-unit-law-compose-hom-Semigroup G H
```

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

### The large precategory of semigroups

```agda
Semigroup-Large-Precategory : Large-Precategory lsuc (_⊔_)
Semigroup-Large-Precategory =
  make-Large-Precategory
    ( Semigroup)
    ( hom-set-Semigroup)
    ( λ {l1} {l2} {l3} {G} {H} {K} → comp-hom-Semigroup G H K)
    ( λ {l} {G} → id-hom-Semigroup G)
    ( λ {l1} {l2} {l3} {l4} {G} {H} {K} {L} →
      associative-comp-hom-Semigroup G H K L)
    ( λ {l1} {l2} {G} {H} → left-unit-law-comp-hom-Semigroup G H)
    ( λ {l1} {l2} {G} {H} → right-unit-law-comp-hom-Semigroup G H)
```

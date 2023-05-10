# The precategory of commutative monoids

```agda
module group-theory.precategory-of-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
```

</details>

## Idea

The **precategory of commutative monoids** consists of commutative monoids and
homomorphisms of monoids.

## Definitions

### The large precategory of commutative monoids

```agda
Commutative-Monoid-Large-Precategory : Large-Precategory lsuc _⊔_
obj-Large-Precategory
  Commutative-Monoid-Large-Precategory =
  Commutative-Monoid
hom-Large-Precategory
  Commutative-Monoid-Large-Precategory =
  hom-Commutative-Monoid
comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = K} {L} {M} =
  comp-hom-Commutative-Monoid K L M
id-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = M} =
  id-hom-Commutative-Monoid M
associative-comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = K} {L} {M} {N} =
  associative-comp-hom-Commutative-Monoid K L M N
left-unit-law-comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = M} {N} =
  left-unit-law-comp-hom-Commutative-Monoid M N
right-unit-law-comp-hom-Large-Precategory
  Commutative-Monoid-Large-Precategory {X = M} {N} =
  right-unit-law-comp-hom-Commutative-Monoid M N
```

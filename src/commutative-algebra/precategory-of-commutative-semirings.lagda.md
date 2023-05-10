# The precategory of commutative semirings

```agda
module commutative-algebra.precategory-of-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import commutative-algebra.commutative-semirings
open import commutative-algebra.homomorphisms-commutative-semirings

open import foundation.universe-levels
```

</details>

## Idea

The **precategory of commutative semirings** consists of commutative semirings
and homomorphisms of semirings.

## Definitions

### The large precategory of commutative semirings

```agda
Commutative-Semiring-Large-Precategory : Large-Precategory lsuc _⊔_
obj-Large-Precategory
  Commutative-Semiring-Large-Precategory =
  Commutative-Semiring
hom-Large-Precategory
  Commutative-Semiring-Large-Precategory =
  hom-Commutative-Semiring
comp-hom-Large-Precategory
  Commutative-Semiring-Large-Precategory {X = A} {B} {C} =
  comp-hom-Commutative-Semiring A B C
id-hom-Large-Precategory
  Commutative-Semiring-Large-Precategory {X = A} =
  id-hom-Commutative-Semiring A
associative-comp-hom-Large-Precategory
  Commutative-Semiring-Large-Precategory {X = A} {B} {C} {D} =
  associative-comp-hom-Commutative-Semiring A B C D
left-unit-law-comp-hom-Large-Precategory
  Commutative-Semiring-Large-Precategory {X = A} {B} =
  left-unit-law-comp-hom-Commutative-Semiring A B
right-unit-law-comp-hom-Large-Precategory
  Commutative-Semiring-Large-Precategory {X = A} {B} =
  right-unit-law-comp-hom-Commutative-Semiring A B
```

### The precategory of commutative semirings of universe level `l`

```agda
Commutative-Semiring-Precategory : (l : Level) → Precategory (lsuc l) l
Commutative-Semiring-Precategory =
  precategory-Large-Precategory Commutative-Semiring-Large-Precategory
```
